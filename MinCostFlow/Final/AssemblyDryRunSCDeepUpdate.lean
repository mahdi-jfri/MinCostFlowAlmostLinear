module

public import MinCostFlow.Final.AssemblyDryRunSCDeepGrid
public import MinCostFlow.MinRatio.WireSelectTouchedWstr
public import MinCostFlow.MinRatio.UpdateAssemblyBase
import MinCostFlow.Chain.Ordered.UpdateProofs
import MinCostFlow.MinRatio.OrdSparseCoreHelpers
import MinCostFlow.IPM.ConnectedInitialConstruction
import Mathlib.Tactic

/-!
# Preservation of `DryChainLenGridInv` across `Update` (`AssemblyDryRunSCDeepUpdate`)

Proves that `DryChainLenGridInv J` (`Final/AssemblyDryRunSCDeepFacts.lean`) is preserved by:
1. `Ordered.algorithm1_update` (`dryChainLenGridInv_update_chain`): on every non-rebuilt level `j`,
   each inserted edge gets `wstr = 1` (preserving the grid and upper bound) while each non-inserted
   surviving edge preserves both `wstr` and `chainLen` (`progTool_nonRebuilt_wstr_and_chainLen_of_not_inserts`);
   on every rebuilt level `j` (including level `0` after `compactGraph`), `T.initOrd` re-establishes
   the `wstr` bounds and `2 ^ (-P)` dyadic grid via `dryInitOrd_wstr_bounds`.
2. `alg2PreLoopState` (`dryChainLenGridInv_preLoop`): specializes to `RefreshBatch` and
   `translateBatch` on any `OrdSolverReachedInv` state.
3. Full `Ordered.algorithm2_updateWith` (`dryChainLenGridInv_update`): combines
   `dryChainLenGridInv_preLoop` with `dryChainLenGridInv_shift` by induction along
   `Ordered.algorithm2_loopWith`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain Chain.Ordered MinCostFlow.Bundle IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Helper lemmas on `compLSFBatch`, `applyBatch`, and `updateLoop` rebuilt suffix -/

/-- If a batch `U` inserts edge `e`, then `(compLSFBatch cs U).wstrGlobal e = 1`. -/
private theorem compLSFBatch_wstr_of_inserts (cs : CompLSFState) :
    ∀ (U : List Update) {e : ℕ}, (∃ u ∈ U, u.Inserts e) →
      (compLSFBatch cs U).wstrGlobal e = 1
  | [], _, ⟨_, hu, _⟩ => by cases hu
  | u :: rest, e, h => by
    change (compLSFBatch (compLSFStepSingle cs u) rest).wstrGlobal e = 1
    by_cases hRest : ∃ u' ∈ rest, u'.Inserts e
    · exact compLSFBatch_wstr_of_inserts (compLSFStepSingle cs u) rest hRest
    · have hu : u.Inserts e := by
        rcases h with ⟨u', hu', hIns⟩
        rcases List.mem_cons.mp hu' with rfl | hmem
        · exact hIns
        · exact absurd ⟨u', hmem, hIns⟩ hRest
      have h1 : (compLSFStepSingle cs u).wstrGlobal e = 1 :=
        compLSFStepSingle_wstr_of_inserts cs hu
      have hNoRest : ∀ u' ∈ rest, ¬ u'.Inserts e := fun u' hu' hIns => hRest ⟨u', hu', hIns⟩
      rw [compLSFBatch_wstr_of_not_inserts _ rest hNoRest, h1]

/-- Any edge `e ∈ (G.applyBatch U).E` that is not inserted by `U` was already in `G.E`. -/
private theorem mem_E_of_mem_applyBatch_of_not_inserts :
    ∀ {G : MGraph} {U : List Update} {e : ℕ},
      e ∈ (G.applyBatch U).E → (∀ u ∈ U, ¬ u.Inserts e) → e ∈ G.E
  | _, [], _, he, _ => he
  | G, u :: rest, e, he, hNo => by
    have h1 : e ∈ (G.applyUpdate u).E :=
      mem_E_of_mem_applyBatch_of_not_inserts he (fun u' hu' => hNo u' (List.mem_cons_of_mem u hu'))
    have hnu : ¬ u.Inserts e := hNo u List.mem_cons_self
    cases u with
    | insert e₀ a b =>
      have hne : e ≠ e₀ := fun heq => hnu (by simpa [Update.Inserts] using heq.symm)
      simpa [MGraph.applyUpdate, hne] using h1
    | delete e₀ =>
      simp only [MGraph.applyUpdate, Finset.mem_erase] at h1
      exact h1.2
    | split v v' St Sh => exact h1

/-- Structural characterization of the rebuilt suffix of `updateLoop`: either level `0` rebuilt
(so `stEnd.G 0 = ((stOrig.G 0).applyBatch U₀).compact`, `stEnd.ℓ = fun j => ℓ' (compactUnrank ...)`,
and every `j < P.d` was re-initialized via `T.initOrd`), or `stEnd.G 0 = (stOrig.G 0).applyBatch U₀`,
`stEnd.ℓ = ℓ'`, and every level `j < P.d` with `firstRebuiltLevel = some iStar` and `iStar ≤ j` was
re-initialized via `T.initOrd`. -/
private theorem updateLoop_rebuilt_initOrd_aux (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ)
    (stOrig : ChainState T P) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      idx + rem = P.d →
      st.rebuildCount = stOrig.rebuildCount →
      st.lvlM = stOrig.lvlM →
      st.N₀ = stOrig.N₀ →
      (0 < idx → st.G 0 = (stOrig.G 0).applyBatch curU ∨ True) →
      (∀ G₀', (idx = 0 → curG = G₀') → (0 < idx → st.G 0 = G₀') →
        let stEnd := (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1
        (firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = some 0 ∧
          stEnd.G 0 = G₀'.compact ∧
          stEnd.ℓ = (fun j => ℓ' (compactUnrank G₀'.E j)) ∧
          ∀ j < P.d,
            stEnd.scState j = T.initOrd P.k (stEnd.lvlM j) stEnd.N₀ (stEnd.G j)
              (stEnd.toTreeChain.chainLen stEnd.ℓ j) (stEnd.toTreeChain.chainGrad stEnd.g j)
              (Chain.Ordered.chainLevelOrd T stEnd.G stEnd.scState stEnd.bran j)) ∨
        (stEnd.G 0 = G₀' ∧ stEnd.ℓ = ℓ' ∧
          ∀ iStar, firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = some iStar →
            0 < iStar ∧
            ∀ j, iStar ≤ j → j < P.d →
              stEnd.scState j = T.initOrd P.k (stEnd.lvlM j) stEnd.N₀ (stEnd.G j)
                (stEnd.toTreeChain.chainLen stEnd.ℓ j) (stEnd.toTreeChain.chainGrad stEnd.g j)
                (Chain.Ordered.chainLevelOrd T stEnd.G stEnd.scState stEnd.bran j))) := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEncAcc hsum hReb _ _ _ G₀' hCur0 hG0
    have hidxEq : idx = P.d := by omega
    subst hidxEq
    dsimp only [Ordered.updateLoop]
    have hNoReb : firstRebuiltLevel P.d stOrig.rebuildCount st.rebuildCount = none := by
      rw [hReb]; exact firstRebuiltLevel_eq_of_eq _
    split_ifs <;>
    · right
      refine ⟨?_, rfl, fun iStar hF => by
        change firstRebuiltLevel P.d stOrig.rebuildCount st.rebuildCount = some iStar at hF
        rw [hNoReb] at hF; cases hF⟩
      by_cases hd0 : P.d = 0
      · simp only [hd0, ↓reduceIte]; exact hCur0 hd0
      · simp only [show (0 : ℕ) ≠ P.d by omega, ↓reduceIte]; exact hG0 (Nat.pos_of_ne_zero hd0)
  | succ rem' ih =>
    intro idx st curG curU curEncAcc hsum hReb hLvlM hN0 _ G₀' hCur0 hG0
    have hidxLt : idx < P.d := by omega
    dsimp only [Ordered.updateLoop]
    by_cases hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length
    · simp only [hOver, ↓reduceIte]
      set stLG : ChainState T P :=
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
      have hfirst : firstRebuiltLevel P.d stOrig.rebuildCount
          (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1.rebuildCount =
          some idx := by
        rw [← hReb]
        simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
        simpa [stLG] using Chain.firstRebuiltLevel_eq_of_inc hidxLt stLG.rebuildCount
      set Ginit := fun j => if j = idx then rebuildStartGraph idx curG else stLG.G j
      obtain ⟨hGpre, _, hCoreSuf⟩ := ordRebuildSuffix_prefix_and_coreAt T L P stLG.lvlM stLG.N₀
        stLG.ℓ stLG.g (P.d - idx) idx (by omega) Ginit stLG.scState stLG.bran stLG.updCount
        stLG.curEnc stLG.curDecUpdates stLG.curFwd
      have hRebCore : ∀ j, idx ≤ j → j < P.d →
          let stEnd := (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1
          stEnd.scState j = T.initOrd P.k (stEnd.lvlM j) stEnd.N₀ (stEnd.G j)
            (stEnd.toTreeChain.chainLen stEnd.ℓ j) (stEnd.toTreeChain.chainGrad stEnd.g j)
            (Chain.Ordered.chainLevelOrd T stEnd.G stEnd.scState stEnd.bran j) := by
        intro j hj1 hj2
        set res := Ordered.rebuildSuffix T L P stLG.lvlM stLG.N₀ stLG.ℓ stLG.g (P.d - idx) idx
          Ginit stLG.scState stLG.bran stLG.updCount stLG.curEnc stLG.curDecUpdates stLG.curFwd
        set stEnd := (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1
        let Cfin : TreeChain :=
          { d := P.d, k := P.k, G := res.1, lsfs := fun r => T.lsfs (res.2.1 r),
            bran := res.2.2.1, S := fun r => T.S (res.2.1 r), emb := fun r => T.emb (res.2.1 r),
            lastK := 1, lastLSFs := fun _ => ⟨res.1 j, ⟨res.1 j, ∅⟩, fun _ => 1⟩, lastBran := 0 }
        have hC : res.2.1 j = T.initOrd P.k (stLG.lvlM j) stLG.N₀ (res.1 j)
            (Cfin.chainLen stLG.ℓ j) (Cfin.chainGrad stLG.g j)
            (Chain.Ordered.chainLevelOrd T res.1 res.2.1 res.2.2.1 j) :=
          (hCoreSuf j hj1 (by omega)).1
        have hStℓ : stEnd.ℓ = stLG.ℓ := by
          simp only [stEnd, Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
        have hStg : stEnd.g = stLG.g := by
          simp only [stEnd, Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
        have hLenEq : ∀ m ≤ j,
            Cfin.chainLen stLG.ℓ m = stEnd.toTreeChain.chainLen stEnd.ℓ m ∧
            Cfin.chainGrad stLG.g m = stEnd.toTreeChain.chainGrad stEnd.g m := by
          intro m
          induction m with
          | zero =>
            intro _
            rw [hStℓ, hStg]
            exact ⟨rfl, rfl⟩
          | succ m ihm =>
            intro hm
            have hmd : m < P.d := lt_of_lt_of_le (Nat.lt_of_succ_le hm) hj2.le
            obtain ⟨hl, hg⟩ := ihm (Nat.le_of_succ_le hm)
            simp only [TreeChain.chainLen, TreeChain.chainGrad]
            rw [hl, hg]
            have hact : Cfin.activeLSF m = stEnd.toTreeChain.activeLSF m := by
              change (if m < P.d then T.lsfs (res.2.1 m) (res.2.2.1 m) else _) =
                (if m < P.d then T.lsfs (stEnd.scState m) (stEnd.bran m) else _)
              rw [ite_eq_left hmd, ite_eq_left hmd]
              dsimp only [stEnd, Ordered.algorithm1_rebuild]
              simp only [hidxLt, ↓reduceDIte]; rfl
            have hGm : Cfin.G m = stEnd.toTreeChain.G m := by
              dsimp only [Cfin, stEnd, ChainState.toTreeChain, Ordered.algorithm1_rebuild]
              simp only [hidxLt, ↓reduceDIte]; rfl
            rw [hact, hGm]
            exact ⟨rfl, rfl⟩
        obtain ⟨hL, hG⟩ := hLenEq j le_rfl
        simpa only [stEnd, res, Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte, hL, hG] using hC
      by_cases h0 : idx = 0
      · subst h0
        left
        refine ⟨hfirst, ?_, ?_, fun j hj => hRebCore j (Nat.zero_le j) hj⟩
        · simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
          rw [hGpre 0 le_rfl]
          simp [Ginit, rebuildStartGraph, hCur0 rfl]
        · simp [Ordered.algorithm1_rebuild, hidxLt, stLG, rebuildStartFn, hCur0 rfl]
      · have hpos : 0 < idx := Nat.pos_of_ne_zero h0
        right
        refine ⟨?_, ?_, fun iStar hF => ?_⟩
        · simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
          rw [hGpre 0 (Nat.zero_le idx)]
          simp only [Ginit, show (0 : ℕ) ≠ idx by omega, ↓reduceIte, stLG]
          exact hG0 hpos
        · simp [Ordered.algorithm1_rebuild, hidxLt, stLG, rebuildStartFn, h0]
        · have heq : iStar = idx := Option.some.inj (hF.symm.trans hfirst)
          subst heq
          exact ⟨hpos, hRebCore⟩
    · simp only [hOver, ↓reduceIte]
      let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      let ℓi := Cpartial.chainLen ℓ' idx
      let gi := Cpartial.chainGrad g' idx
      let ord_i := chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx
      let upd := T.updateOrd (st.scState idx) curU ℓi gi ord_i
      let nextG := T.S upd.1 (st.bran idx)
      let nextU := upd.2 (st.bran idx)
      let stNext : ChainState T P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then upd.1 else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j =>
            if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
          curFwd := fun j =>
            if j = idx then st.curFwd idx + nextU.length else st.curFwd j
          curEnc := fun j =>
            if j = idx then st.curEnc idx + curEncAcc
            else if j = idx + 1 then st.curEnc (idx + 1) + (st.G (idx + 1)).batchEnc nextU
            else st.curEnc j
          curDecUpdates := fun j =>
            if j = idx then
              st.curDecUpdates idx +
                (diffTreeChanges (T.lsfs (st.scState idx) (st.bran idx)).F.F.E
                  (T.lsfs upd.1 (st.bran idx)).F.F.E).length
            else st.curDecUpdates j }
      exact ih (idx + 1) stNext nextG nextU 0 (by omega) hReb hLvlM hN0 (fun _ => Or.inr trivial)
        G₀' (fun h => absurd h (Nat.succ_ne_zero idx)) (fun _ => by
          by_cases h0 : idx = 0
          · subst h0; simp only [stNext, ↓reduceIte]; exact hCur0 rfl
          · simp only [stNext, show (0 : ℕ) ≠ idx by omega, ↓reduceIte]
            exact hG0 (Nat.pos_of_ne_zero h0))

private theorem algorithm1_update_rebuilt_initOrd (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U₀ : List Update) (g' ℓ' : ℕ → ℝ) :
    let st' := (Ordered.algorithm1_update T L TP P N₀ st U₀ g' ℓ').1
    (firstRebuiltLevel P.d st.rebuildCount st'.rebuildCount = some 0 ∧
      st'.G 0 = ((st.G 0).applyBatch U₀).compact ∧
      st'.ℓ = (fun j => ℓ' (compactUnrank ((st.G 0).applyBatch U₀).E j)) ∧
      ∀ j < P.d,
        st'.scState j = T.initOrd P.k (st'.lvlM j) st'.N₀ (st'.G j)
          (st'.toTreeChain.chainLen st'.ℓ j) (st'.toTreeChain.chainGrad st'.g j)
          (Chain.Ordered.chainLevelOrd T st'.G st'.scState st'.bran j)) ∨
    (st'.G 0 = (st.G 0).applyBatch U₀ ∧ st'.ℓ = ℓ' ∧
      ∀ iStar, firstRebuiltLevel P.d st.rebuildCount st'.rebuildCount = some iStar →
        0 < iStar ∧
        ∀ j, iStar ≤ j → j < P.d →
          st'.scState j = T.initOrd P.k (st'.lvlM j) st'.N₀ (st'.G j)
            (st'.toTreeChain.chainLen st'.ℓ j) (st'.toTreeChain.chainGrad st'.g j)
            (Chain.Ordered.chainLevelOrd T st'.G st'.scState st'.bran j)) :=
  updateLoop_rebuilt_initOrd_aux T L TP P N₀ ℓ' g' st P.d 0
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U₀.length else st.recUpdates j }
    ((st.G 0).applyBatch U₀) U₀ ((st.G 0).batchEnc U₀) (Nat.zero_add _) rfl rfl rfl
    (fun _ => Or.inr trivial) ((st.G 0).applyBatch U₀) (fun _ => rfl)
    (fun h => absurd h (Nat.lt_irrefl 0))

/-! ## 2. Preservation of `DryChainLenGridInv` across `Ordered.algorithm1_update` -/

/-- **`DryChainLenGridInv` is preserved by `Ordered.algorithm1_update`** whenever the new level-`0`
graph and lengths satisfy `LengthsWithin` and `IsDyadicGrid` and agree with `ch.ℓ` on surviving
non-inserted edges. -/
theorem dryChainLenGridInv_update_chain (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hLoopInv : Ordered.ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch)
    (hGridInv : DryChainLenGridInv J ch)
    {U₀ : List Update} {g' ℓ' : ℕ → ℝ}
    (hBatch₀ : (ch.G 0).BatchIsValid U₀)
    (hNR₀ : NoBatchReinsert (ch.G 0) U₀)
    (hEdge : ∀ u ∈ U₀, IsEdgeUpdate u)
    (hG0'Valid : ((ch.G 0).applyBatch U₀).IsValid)
    (hG0'm : ((ch.G 0).applyBatch U₀).m ≤ (solverConnectedAugmented J).m)
    (hG0'n : ((ch.G 0).applyBatch U₀).n ≤ 2 * (solverConnectedAugmented J).m + 2)
    (hLenWithin :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IPM.LengthsWithin ((ch.G 0).applyBatch U₀) (ipmQualityRangeExponent I.m V k) ℓ')
    (hGrid :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IsDyadicGrid ((ch.G 0).applyBatch U₀) (ipmQualityPrecision I.m V k) ℓ')
    (hℓ'Stable : ∀ e ∈ ((ch.G 0).applyBatch U₀).E, e ∈ (ch.G 0).E →
      (∀ u ∈ U₀, ¬ u.Inserts e) → ℓ' e = ch.ℓ e) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    DryChainLenGridInv J (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ch U₀ g' ℓ').1 := by
  intro cfg
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let E := ipmQualityRangeExponent I.m V k
  let P := ipmQualityPrecision I.m V k
  let L := ipmQualityLimbs I.m V k
  let depth := Expander.chosenL (cfg.P.M₀ ^ 2)
  have hV : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hEΨ : (E : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hℓ'R : LenInRange (max 0 cfg.Ψ) ((ch.G 0).applyBatch U₀) ℓ' := by
    intro e he
    have hlo := (hLenWithin e he).1
    have hhi := (hLenWithin e he).2
    have hpos : 0 < ℓ' e := lt_of_lt_of_le (by positivity) hlo
    have hlog : |Real.log (ℓ' e)| ≤ max 0 cfg.Ψ :=
      ((abs_log_le_of_two_pow_bounds hlo hhi).trans hEΨ).trans (le_max_right 0 cfg.Ψ)
    rw [abs_le] at hlog
    exact ⟨by simpa [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog.1,
      by simpa [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog.2⟩
  have hG0'mM0 : ((ch.G 0).applyBatch U₀).m ≤ cfg.P.M₀ := hG0'm.trans (le_max_left _ _)
  have hG0'nN0 : ((ch.G 0).applyBatch U₀).n ≤ cfg.N₀ := by
    have hG0'n' : ((ch.G 0).applyBatch U₀).n ≤ 2 * I.m + 2 := hG0'n
    have hImM0 : I.m ≤ cfg.P.M₀ := le_max_left _ _
    have hN0eq : cfg.N₀ = 4 * cfg.P.M₀ := rfl
    have hM2 : 2 ≤ cfg.P.M₀ :=
      (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _)
    omega
  obtain ⟨hInv, ⟨overflow, hBud⟩, _, _⟩ := hLoopInv
  have hUpd := update_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud U₀ g' ℓ'
    hBatch₀ hNR₀ hEdge hG0'Valid hG0'mM0 hG0'nN0 hℓ'R hℓ'Stable
  set ch' := (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ch U₀ g' ℓ').1
  have hInv' : Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' := hUpd.1
  have hB' := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hInv'
  have hH := (hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hH' := (hInv'.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hT : cfg.T = sparseCoreProgTool (dryLSFInitUsed L P) dryCLsstUsed depth sparsifyImplUsed := rfl
  have hInit : ∀ b < cfg.P.k, IsValidLSFInitFor (dryLSFInitUsed L P) dryCLsstUsed cfg.P.k b :=
    fun b hb => dryLSFInitUsed_isValidLSFInitFor L P cfg.P.k b hb
  have hStruct := algorithm1_update_rebuilt_initOrd cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ch U₀ g' ℓ'
  dsimp only at hStruct
  -- Common induction helper: given level-0 bounds and a per-level branch-wstr constructor,
  -- prove `DryChainLenGridInv J ch'`.
  let LvlP (j : ℕ) : Prop :=
    (∀ e ∈ (ch'.G j).E, (2 : ℝ) ^ (-(E : ℤ)) ≤ ch'.toTreeChain.chainLen ch'.ℓ j e ∧
      ch'.toTreeChain.chainLen ch'.ℓ j e ≤ (2 : ℝ) ^ (E + j * (3 * I.m.size + 12))) ∧
    IsDyadicGrid (ch'.G j) P (ch'.toTreeChain.chainLen ch'.ℓ j)
  let BrP (j : ℕ) : Prop :=
    ∀ b < cfg.P.k, ∀ e ∈ (ch'.G j).E,
      1 ≤ (cfg.T.lsfs (ch'.scState j) b).wstr e ∧
      (cfg.T.lsfs (ch'.scState j) b).wstr e * ch'.toTreeChain.chainLen ch'.ℓ j e ≤
        (2 : ℝ) ^ (E + (j + 1) * (3 * I.m.size + 12)) ∧
      ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P =
        (cfg.T.lsfs (ch'.scState j) b).wstr e * ch'.toTreeChain.chainLen ch'.ℓ j e
  have hBuild :
      (ch'.G 0).m ≤ I.m → (ch'.G 0).n ≤ 2 * I.m + 2 →
      ((∀ e ∈ (ch'.G 0).E, (2 : ℝ) ^ (-(E : ℤ)) ≤ ch'.ℓ e ∧ ch'.ℓ e ≤ (2 : ℝ) ^ E) ∧
        IsDyadicGrid (ch'.G 0) P ch'.ℓ) →
      (∀ j < cfg.P.d, LvlP j → BrP j) → DryChainLenGridInv J ch' := by
    intro hm0 hn0 hLvl0 hBrStep
    have hMain : ∀ j ≤ cfg.P.d, LvlP j ∧ (j < cfg.P.d → BrP j) := by
      intro j
      induction j with
      | zero =>
        intro _
        have h0 : LvlP 0 := by simpa [LvlP, TreeChain.chainLen] using hLvl0
        exact ⟨h0, fun hj => hBrStep 0 hj h0⟩
      | succ j ih =>
        intro hjLe
        have hjLt : j < cfg.P.d := hjLe
        obtain ⟨hPrevLvl, hPrevBr⟩ := ih (Nat.le_of_lt hjLt)
        have hSubE : (ch'.G (j + 1)).E ⊆ (ch'.G j).E := chainInv_G_succ_E_subset hV hInv' hjLt
        have hBrJ := hPrevBr hjLt (ch'.bran j) (hInv'.hBran j hjLt)
        have hCurLvl : LvlP (j + 1) := by
          refine ⟨fun e he => ?_, fun e he => ?_⟩
          · have hej : e ∈ (ch'.G j).E := hSubE he
            obtain ⟨hw1, hhi, _⟩ := hBrJ e hej
            have hlo := (hPrevLvl.1 e hej).1
            have hpos : (0 : ℝ) ≤ ch'.toTreeChain.chainLen ch'.ℓ j e := le_trans (by positivity) hlo
            have hcl : ch'.toTreeChain.chainLen ch'.ℓ (j + 1) e =
                (cfg.T.lsfs (ch'.scState j) (ch'.bran j)).wstr e *
                  ch'.toTreeChain.chainLen ch'.ℓ j e := by
              simp only [TreeChain.chainLen, coreLen, TreeChain.activeLSF, ChainState.toTreeChain,
                hjLt, ↓reduceIte]
            rw [hcl]
            refine ⟨?_, hhi⟩
            calc (2 : ℝ) ^ (-(E : ℤ)) ≤ ch'.toTreeChain.chainLen ch'.ℓ j e := hlo
              _ = 1 * ch'.toTreeChain.chainLen ch'.ℓ j e := (one_mul _).symm
              _ ≤ (cfg.T.lsfs (ch'.scState j) (ch'.bran j)).wstr e *
                    ch'.toTreeChain.chainLen ch'.ℓ j e := mul_le_mul_of_nonneg_right hw1 hpos
          · have hej : e ∈ (ch'.G j).E := hSubE he
            obtain ⟨_, _, hq⟩ := hBrJ e hej
            simpa [TreeChain.chainLen, coreLen, TreeChain.activeLSF, ChainState.toTreeChain, hjLt] using hq
        exact ⟨hCurLvl, fun hj1Lt => hBrStep (j + 1) hj1Lt hCurLvl⟩
    refine ⟨hm0, hn0, fun j hj => (hMain j hj).1, fun j hj => (hMain j hj.le).2 hj, ?_⟩
    rcases algorithm1_update_lastLSFs_or_build cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ch U₀ g' ℓ' with hEq | ⟨ℓd, hB⟩
    · rw [hEq]; exact hGridInv.2.2.2.2
    · exact ⟨ch'.G cfg.P.d, ℓd, (Finset.card_le_card (chainInv_G_E_subset_G0 hV hInv' cfg.P.d le_rfl)).trans hm0, hB⟩
  have hRebuiltLevel :
      (ch'.G 0).m ≤ I.m → (ch'.G 0).n ≤ 2 * I.m + 2 →
      ∀ j < cfg.P.d,
        ch'.scState j = cfg.T.initOrd cfg.P.k (ch'.lvlM j) ch'.N₀ (ch'.G j)
          (ch'.toTreeChain.chainLen ch'.ℓ j) (ch'.toTreeChain.chainGrad ch'.g j)
          (Chain.Ordered.chainLevelOrd cfg.T ch'.G ch'.scState ch'.bran j) →
        LvlP j → BrP j := by
    intro hm0 hn0 j hj hSc hCurLvl b hb e he
    have hBj := hB' j (Nat.le_of_lt hj)
    have hSubE0 : (ch'.G j).E ⊆ (ch'.G 0).E := chainInv_G_E_subset_G0 hV hInv' j (Nat.le_of_lt hj)
    have hGjM : (ch'.G j).m ≤ I.m := (Finset.card_le_card hSubE0).trans hm0
    have hGjN : (ch'.G j).n ≤ 2 * I.m + 2 := (Finset.card_le_card hBj.2.1).trans hn0
    rw [hSc]
    exact dryInitOrd_wstr_bounds J hJn hJm hCap hBj.1 hGjN hGjM hCurLvl.1 hCurLvl.2 hb he
  rcases hStruct with ⟨_, hG0Comp, hℓComp, hAllInit⟩ | ⟨hG0Eq, hℓEq, hSufInit⟩
  · -- Case 1: Level `0` was rebuilt (`compactGraph` + `compactUnrank`)
    have hm0 : (ch'.G 0).m ≤ I.m := by
      have : ((ch.G 0).applyBatch U₀).compact.m = ((ch.G 0).applyBatch U₀).m := by
        simp [MGraph.compact, MGraph.m]
      rw [hG0Comp, this]; exact hG0'm
    have hn0 : (ch'.G 0).n ≤ 2 * I.m + 2 := by
      have : ((ch.G 0).applyBatch U₀).compact.n = ((ch.G 0).applyBatch U₀).n := by
        simp [MGraph.compact, MGraph.n]
      rw [hG0Comp, this]; exact hG0'n
    have hLvl0 :
        (∀ e ∈ (ch'.G 0).E, (2 : ℝ) ^ (-(E : ℤ)) ≤ ch'.ℓ e ∧ ch'.ℓ e ≤ (2 : ℝ) ^ E) ∧
        IsDyadicGrid (ch'.G 0) P ch'.ℓ := by
      rw [hG0Comp, hℓComp]
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · have hlt : j < ((ch.G 0).applyBatch U₀).E.card := by
          simpa [MGraph.compact] using hj
        exact hLenWithin _ (compactUnrank_mem hlt)
      · have hlt : j < ((ch.G 0).applyBatch U₀).E.card := by
          simpa [MGraph.compact] using hj
        exact hGrid _ (compactUnrank_mem hlt)
    exact hBuild hm0 hn0 hLvl0 (fun j hj hCur => hRebuiltLevel hm0 hn0 j hj (hAllInit j hj) hCur)
  · -- Case 2: Level `0` did NOT rebuild (`ch'.G 0 = (ch.G 0).applyBatch U₀`, `ch'.ℓ = ℓ'`)
    have hm0 : (ch'.G 0).m ≤ I.m := hG0Eq ▸ hG0'm
    have hn0 : (ch'.G 0).n ≤ 2 * I.m + 2 := hG0Eq ▸ hG0'n
    have hLvl0 :
        (∀ e ∈ (ch'.G 0).E, (2 : ℝ) ^ (-(E : ℤ)) ≤ ch'.ℓ e ∧ ch'.ℓ e ≤ (2 : ℝ) ^ E) ∧
        IsDyadicGrid (ch'.G 0) P ch'.ℓ := by
      rw [hG0Eq, hℓEq]; exact ⟨hLenWithin, hGrid⟩
    have hNR_cases := progTool_algorithm1_update_nonRebuiltBatches hInv hH hH' hInit hBatch₀ hNR₀
    rcases hNR_cases with (hF0 | ⟨hd0, _⟩) | ⟨iNR, U, hU0, hCase, hNR⟩
    · -- Contradiction: `firstRebuiltLevel = some 0` contradicts `0 < 0` from `hSufInit`
      exact absurd (hSufInit 0 hF0).1 (lt_irrefl 0)
    · have hd0' : cfg.P.d = 0 := hd0
      exact hBuild hm0 hn0 hLvl0 (fun j hj => by omega)
    · obtain ⟨_, _, _, hBrOld, _⟩ := hGridInv
      have hℓEq0 : ∀ f ∈ (ch'.G 0).E, f ∈ (ch.G 0).E → ch'.ℓ f = ch.ℓ f := by
        intro f hf' hf; rw [hG0Eq] at hf'; rw [hℓEq]; exact hℓ'Stable f hf' hf (hNR₀ f hf)
      refine hBuild hm0 hn0 hLvl0 fun j hj hCurLvl b hb e he => ?_
      by_cases hjNR : j ≤ iNR
      · obtain ⟨_, ℓj, gj, ordj, hsc'_raw, _⟩ := hNR.2.2.2.1 j hjNR hj
        have hsc' : ch'.scState j = (cfg.T.updateOrd (ch.scState j) (U j) ℓj gj ordj).1 := hsc'_raw
        by_cases hne : (ch.scState j).isNonempty = true
        · have hup := asm_updateOrd_of_nonempty (dryLSFInitUsed L P) dryCLsstUsed depth
            (fun _ => canonicalSparsify sparsifyImplUsed) (canonicalSparsifyParams sparsifyImplUsed)
            (dsAmortConst sparsifyImplUsed) (ch.scState j) hne (U j) ℓj gj ordj
          have hne' : (ch'.scState j).isNonempty = true := by
            rw [hsc']; change ((sparseCoreBundleRestartToolMachWith (dryLSFInitUsed L P) dryCLsstUsed
              depth (fun _ => canonicalSparsify sparsifyImplUsed)
              (canonicalSparsifyParams sparsifyImplUsed) (dsAmortConst sparsifyImplUsed)).updateOrd
              (ch.scState j) (U j) ℓj gj ordj).1.isNonempty = true
            rw [hup]; exact hne
          have hWstrNew : (cfg.T.lsfs (ch'.scState j) b).wstr e =
              (compLSFBatch ((ch.scState j).trees b).cs (U j)).wstrGlobal e := by
            change (if (ch'.scState j).isNonempty then _ else emptyLSF).wstr e = _
            rw [ite_eq_left hne', hsc']
            change (((sparseCoreBundleRestartToolMachWith (dryLSFInitUsed L P) dryCLsstUsed depth
              (fun _ => canonicalSparsify sparsifyImplUsed)
              (canonicalSparsifyParams sparsifyImplUsed) (dsAmortConst sparsifyImplUsed)).updateOrd
              (ch.scState j) (U j) ℓj gj ordj).1.trees b).cs.lsf.wstr e = _
            rw [hup]; rfl
          by_cases hIns : ∃ u ∈ U j, u.Inserts e
          · -- Edge `e` inserted by `U j`: `wstr e = 1`
            have hw1 : (cfg.T.lsfs (ch'.scState j) b).wstr e = 1 :=
              hWstrNew.trans (compLSFBatch_wstr_of_inserts _ (U j) hIns)
            rw [hw1, one_mul]
            exact ⟨le_refl 1, (hCurLvl.1 e he).2.trans (pow_le_pow_right₀ (by norm_num)
              (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ j)) E)), hCurLvl.2 e he⟩
          · -- Edge `e` NOT inserted by `U j`: survives from `ch.G j`, keeps `wstr` and `chainLen`
            have hNoIns : ∀ u ∈ U j, ¬ u.Inserts e := fun u hu hi => hIns ⟨u, hu, hi⟩
            have hGjEq : ch'.G j = (ch.G j).applyBatch (U j) := (hNR.2.2.1 j hjNR).1
            have heOld : e ∈ (ch.G j).E :=
              mem_E_of_mem_applyBatch_of_not_inserts (hGjEq ▸ he) hNoIns
            have hWstrEq : (cfg.T.lsfs (ch'.scState j) b).wstr e =
                (cfg.T.lsfs (ch.scState j) b).wstr e := by
              rw [hWstrNew, compLSFBatch_wstr_of_not_inserts _ (U j) hNoIns]
              change _ = (if (ch.scState j).isNonempty then _ else emptyLSF).wstr e
              rw [ite_eq_left hne]; rfl
            have hCLEq : ch'.toTreeChain.chainLen ch'.ℓ j e =
                ch.toTreeChain.chainLen ch.ℓ j e := by
              cases j with
              | zero =>
                change ch'.ℓ e = ch.ℓ e
                exact hℓEq0 e he heOld
              | succ m =>
                have hmNR : m ≤ iNR := Nat.le_of_succ_le hjNR
                have hNoAll := progTool_nonRebuilt_not_inserts_of_top hInv hH hH' hNR
                  (m + 1) hjNR e he heOld hNoIns
                have hNoM : ∀ u ∈ U m, ¬ u.Inserts e := hNoAll m (Nat.le_succ m)
                have hmd : m < cfg.P.d := Nat.lt_of_succ_lt hj
                have heM' : e ∈ (ch'.G m).E :=
                  (Finset.mem_sdiff.mp (ch'.toTreeChain.G_succ_E_subset hH' hmd he)).1
                have heM : e ∈ (ch.G m).E :=
                  (Finset.mem_sdiff.mp (ch.toTreeChain.G_succ_E_subset hH hmd heOld)).1
                exact (progTool_nonRebuilt_wstr_and_chainLen_of_not_inserts hInv hH hH' hNR hℓEq0
                  m hmNR e heM' heM hNoM).2
            rw [hWstrEq, hCLEq]
            exact hBrOld j hj b hb e heOld
        · have hf : (ch.scState j).isNonempty = false := Bool.eq_false_iff.mpr hne
          have hup := asm_updateOrd_of_empty (dryLSFInitUsed L P) dryCLsstUsed depth
            (fun _ => canonicalSparsify sparsifyImplUsed) (canonicalSparsifyParams sparsifyImplUsed)
            (dsAmortConst sparsifyImplUsed) (ch.scState j) hf (U j) ℓj gj ordj
          have hne' : (ch'.scState j).isNonempty = false := by
            rw [hsc']; change ((sparseCoreBundleRestartToolMachWith (dryLSFInitUsed L P) dryCLsstUsed
              depth (fun _ => canonicalSparsify sparsifyImplUsed)
              (canonicalSparsifyParams sparsifyImplUsed) (dsAmortConst sparsifyImplUsed)).updateOrd
              (ch.scState j) (U j) ℓj gj ordj).1.isNonempty = false
            rw [hup]; exact hf
          have hw1 : (cfg.T.lsfs (ch'.scState j) b).wstr e = 1 := by
            change (if (ch'.scState j).isNonempty then _ else emptyLSF).wstr e = 1
            simp [hne', emptyLSF]
          rw [hw1, one_mul]
          exact ⟨le_refl 1, (hCurLvl.1 e he).2.trans (pow_le_pow_right₀ (by norm_num)
            (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ j)) E)), hCurLvl.2 e he⟩
      · rcases hCase with ⟨hF, _⟩ | ⟨_, hEqD | ⟨hEqD, _⟩⟩
        · exact hRebuiltLevel hm0 hn0 j hj ((hSufInit (iNR + 1) hF).2 j (by omega) hj) hCurLvl b hb e he
        · have hEqD' : iNR = cfg.P.d := hEqD; omega
        · have hEqD' : iNR + 1 = cfg.P.d := hEqD; omega

/-! ## 3. Preservation across `alg2PreLoopState` and full `Ordered.algorithm2_updateWith` -/

/-- Combined pre-loop preservation from `OrdSolverReached` directly: on any reached solver state
with a `RefreshBatch` whose new lengths lie in `LengthsWithin` and `IsDyadicGrid` and satisfy
`hagree`, `pre := alg2PreLoopState cfg model U_ext g_ext l_ext` satisfies both
`DryChainLenGridInv J pre.chain` and `Ordered.ShiftLoopChainInv cfg pre.chain`. -/
theorem dryChainLenGridInv_preLoop_of_reached (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {κ : ℝ}
    {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    (hReached : OrdSolverReached (concreteCirculationCfgWithLast dryWitnessUsed J) κ
      (namedInstance (solverConnectedAugmented J)) model)
    (hGridInv : DryChainLenGridInv J model.chain)
    {U_ext : List Update} {g_ext l_ext : ℕ → ℝ}
    (hU : RefreshBatch (namedInstance (solverConnectedAugmented J)) U_ext)
    (hLenWithin : IPM.LengthsWithin (namedInstance (solverConnectedAugmented J))
      (ipmQualityRangeExponent (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m)) l_ext)
    (hGrid : IsDyadicGrid (namedInstance (solverConnectedAugmented J))
      (ipmQualityPrecision (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m)) l_ext)
    (hagree : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      (∀ u ∈ U_ext, ¬ u.Inserts e) → g_ext e = model.extg e ∧ l_ext e = model.extℓ e) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let pre := alg2PreLoopState cfg model U_ext g_ext l_ext
    DryChainLenGridInv J pre.chain ∧ Ordered.ShiftLoopChainInv cfg pre.chain := by
  intro cfg pre
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let G := namedInstance I
  have hV : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of
    (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
    (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap
  have hmG : G.m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
  have hnG : G.n ≤ cfg.N₀ := by
    have hInEq : G.n = I.n := by simp [G, namedInstance, MGraph.n]
    rw [hInEq]; exact hIn
  have hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v :=
    connectedInitialInstance_connected J.toInstance (V : ℤ)
  have hEΨ : ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  obtain ⟨D, η, op, T_step, hHist, hEdgeD, hLenD, hGD, hEq⟩ := hReached
  have hUncond := (algorithm2_uncond_preserves_with (η := η) κ hV hHist hEdgeD hLenD
    (fun t ht => by rw [hGD t ht]; exact hmG) (fun t ht => by rw [hGD t ht]; exact hnG)).1
    T_step le_rfl
  rw [← hEq] at hUncond
  rcases hUncond with ⟨hInv, hBud, _, _, hFresh, hExtG, hExtLG, hChℓ, _, _, _, _, _, _, _⟩
  have hGT : D.G T_step = G := hGD T_step le_rfl
  have hExtG_G : model.extG = G := hExtG.trans hGT
  have hGValid : G.IsValid := hGT ▸ (hHist.2.1 T_step le_rfl).1
  set tb := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U_ext
  have hTB := translateBatch_preserves U_ext model.extG (model.chain.G 0)
    model.extToInt model.intToExt model.nextFresh hFresh (hExtG_G.symm ▸ hU.1)
  dsimp only at hTB
  rcases hTB with ⟨hExtG', hFresh', hBatch_int, hNR_int, _, _, _, hi2e_old, _, hYesInsExt⟩
  have hExtEq : tb.1 = G := by rw [hExtG', hExtG_G]; exact hU.2.1
  have hEdgeU : ∀ u ∈ U_ext, IsEdgeUpdate u := fun u hu => by
    have hns := hU.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact absurd hns id
  have hEdge_int : ∀ u' ∈ tb.2.2.2.2, IsEdgeUpdate u' :=
    translateBatch_isEdgeUpdate model.extG model.extToInt model.intToExt model.nextFresh U_ext hEdgeU
  have hG0'Valid : ((model.chain.G 0).applyBatch tb.2.2.2.2).IsValid :=
    hFresh'.isValid_iff.mpr (hExtEq ▸ hGValid)
  have hG0'm : ((model.chain.G 0).applyBatch tb.2.2.2.2).m ≤ I.m := by
    rw [hFresh'.m_eq, hExtEq, namedInstance_m]
  have hG0'n : ((model.chain.G 0).applyBatch tb.2.2.2.2).n ≤ 2 * I.m + 2 := by
    rw [hFresh'.n_eq, hExtEq]
    have hInEq : G.n = I.n := by simp [G, namedInstance, MGraph.n]
    have hImGeJm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
    rw [hInEq]; change J.n + 1 ≤ 2 * I.m + 2; omega
  have hLenInt : IPM.LengthsWithin ((model.chain.G 0).applyBatch tb.2.2.2.2)
      (ipmQualityRangeExponent I.m V k) (fun e' => l_ext (tb.2.2.1 e')) := fun e' he' => by
    have heG : tb.2.2.1 e' ∈ G.E := hExtEq ▸ (hFresh'.hRight e' he').2
    exact hLenWithin _ heG
  have hGridInt : IsDyadicGrid ((model.chain.G 0).applyBatch tb.2.2.2.2)
      (ipmQualityPrecision I.m V k) (fun e' => l_ext (tb.2.2.1 e')) := fun e' he' => by
    have heG : tb.2.2.1 e' ∈ G.E := hExtEq ▸ (hFresh'.hRight e' he').2
    exact hGrid _ heG
  have hLenToR : ∀ (H : MGraph) (f : ℕ → ℝ),
      IPM.LengthsWithin H (ipmQualityRangeExponent I.m V k) f → LenInRange (max 0 cfg.Ψ) H f := by
    intro H f hW e he
    have hpos : 0 < f e := lt_of_lt_of_le (by positivity) (hW e he).1
    have hlog := abs_le.mp (((abs_log_le_of_two_pow_bounds (hW e he).1 (hW e he).2).trans hEΨ).trans
      (le_max_right 0 cfg.Ψ))
    exact ⟨by simpa [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog.1,
      by simpa [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog.2⟩
  have hℓ_intR := hLenToR _ _ hLenInt
  have hℓ_intStable : ∀ e' ∈ ((model.chain.G 0).applyBatch tb.2.2.2.2).E, e' ∈ (model.chain.G 0).E →
      (∀ u' ∈ tb.2.2.2.2, ¬ u'.Inserts e') →
      (fun e' => l_ext (tb.2.2.1 e')) e' = model.chain.ℓ e' := by
    intro e' he' he0 _
    have hlt : e' < model.nextFresh := hFresh.hLtFresh e' he0
    have hi2e_eq : tb.2.2.1 e' = model.intToExt e' := hi2e_old e' hlt
    have heExt : model.intToExt e' ∈ G.E := by
      rw [← hExtEq, ← hi2e_eq]; exact (hFresh'.hRight e' he').2
    have hNoIns : ∀ u ∈ U_ext, ¬ u.Inserts (model.intToExt e') := fun u hu hIns => by
      have hge := hYesInsExt (model.intToExt e') (hExtEq ▸ heExt) ⟨u, hu, hIns⟩
      have he2i'_eq : tb.2.1 (model.intToExt e') = e' := by
        rw [← hi2e_eq]; exact (hFresh'.hRight e' he').1
      exact absurd (lt_of_lt_of_le hlt (le_trans hge (le_of_eq he2i'_eq))) (lt_irrefl _)
    dsimp only
    rw [hi2e_eq, (hagree _ heExt hNoIns).2, hChℓ]
  have hConnOfFresh : ∀ {H : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ},
      FreshInv G H e2i i2e nf → ∀ u ∈ H.V, ∀ v ∈ H.V, H.Connected u v := by
    intro H e2i i2e nf hF
    have hWalk : ∀ {a b : ℕ} {P : List (ℕ × Bool)}, G.IsWalk a b P → H.Connected a b := by
      intro a b P hW
      induction hW with
      | nil u => exact ⟨[], .nil u⟩
      | @cons u v x P hx hsrc _ ih =>
        obtain ⟨P', hP'⟩ := ih
        have heInt : e2i x.1 ∈ H.E := hF.hE ▸ Finset.mem_image_of_mem _ hx
        have htail := hF.hTail x.1 hx
        have hhead := hF.hHead x.1 hx
        have hsrc' : H.src (e2i x.1, x.2) = u := by
          by_cases hb : x.2 = true <;> simpa [MGraph.src, hb, htail, hhead] using hsrc
        have hdst' : H.dst (e2i x.1, x.2) = G.dst x := by
          by_cases hb : x.2 = true <;> simp [MGraph.dst, hb, htail, hhead]
        exact ⟨(e2i x.1, x.2) :: P', .cons heInt hsrc' (hdst'.symm ▸ hP')⟩
    intro u hu v hv
    obtain ⟨P, hP⟩ := hConn u (hF.hV ▸ hu) v (hF.hV ▸ hv)
    exact hWalk hP
  have hℓ0R : LenInRange (max 0 cfg.Ψ) (model.chain.G 0) model.chain.ℓ := by
    intro e' he0
    have heExt : model.intToExt e' ∈ (D.G T_step).E := hExtG ▸ (hFresh.hRight e' he0).2
    have hpos := (hHist.2.1 T_step le_rfl).2 _ heExt
    have hlog := hLenD T_step le_rfl _ heExt
    have hmax : |Real.log (D.ℓ T_step (model.intToExt e'))| ≤ max 0 cfg.Ψ :=
      le_trans hlog (le_max_right _ _)
    rw [abs_le] at hmax
    have hEqℓ : model.chain.ℓ e' = D.ℓ T_step (model.intToExt e') := by
      rw [hChℓ]; exact (hExtLG _ (hExtG ▸ heExt)).1
    rw [hEqℓ]
    exact ⟨by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hmax.1,
      by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hmax.2⟩
  have hShift : ShiftLoopChainInv cfg model.chain :=
    ⟨hInv, ⟨_, hBud⟩, hℓ0R, hConnOfFresh (hExtG_G ▸ hFresh)⟩
  have hPreGrid : DryChainLenGridInv J pre.chain :=
    dryChainLenGridInv_update_chain J hJn hJm hCap hShift hGridInv
      hBatch_int hNR_int hEdge_int hG0'Valid hG0'm hG0'n hLenInt hGridInt hℓ_intStable
  have hUpd := update_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud tb.2.2.2.2
    (fun e' => g_ext (tb.2.2.1 e')) (fun e' => l_ext (tb.2.2.1 e'))
    hBatch_int hNR_int hEdge_int hG0'Valid (hG0'm.trans (le_max_left _ _))
    (by rw [hFresh'.n_eq, hExtEq]; exact hnG) hℓ_intR hℓ_intStable
  have hRen := update_freshInv_renamed cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain g_ext l_ext hFresh'
  dsimp only at hRen
  have hFreshPre : FreshInv G (pre.chain.G 0) pre.extToInt pre.intToExt pre.nextFresh :=
    hExtEq ▸ hRen.1
  have hPreℓR : LenInRange (max 0 cfg.Ψ) (pre.chain.G 0) pre.chain.ℓ :=
    hLenToR _ _ fun e' he' => by
      have hℓe : pre.chain.ℓ e' = l_ext (pre.intToExt e') := congrFun hRen.2.1 e'
      rw [hℓe]; exact hLenWithin _ (hFreshPre.hRight e' he').2
  exact ⟨hPreGrid, ⟨hUpd.1, ⟨_, hUpd.2.1⟩, hPreℓR, hConnOfFresh hFreshPre⟩⟩

/-- Combined pre-loop preservation from `OrdSolverReachedInv`. -/
theorem dryChainLenGridInv_preLoop_and_inv (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {L : ℕ} {Rcore : DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T)}
    {κ : ℝ} {P_inv : ℕ}
    {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    {tok : SolverToken (concreteCirculationCfgWithLast dryWitnessUsed J) L Rcore}
    (hReached : OrdSolverReachedInv κ (namedInstance (solverConnectedAugmented J)) P_inv model tok)
    (hGridInv : DryChainLenGridInv J model.chain)
    {U_ext : List Update} {g_ext l_ext : ℕ → ℝ}
    (hU : RefreshBatch (namedInstance (solverConnectedAugmented J)) U_ext)
    (hLenWithin : IPM.LengthsWithin (namedInstance (solverConnectedAugmented J))
      (ipmQualityRangeExponent (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m)) l_ext)
    (hGrid : IsDyadicGrid (namedInstance (solverConnectedAugmented J))
      (ipmQualityPrecision (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m)) l_ext)
    (hagree : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      (∀ u ∈ U_ext, ¬ u.Inserts e) → g_ext e = model.extg e ∧ l_ext e = model.extℓ e) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let pre := alg2PreLoopState cfg model U_ext g_ext l_ext
    DryChainLenGridInv J pre.chain ∧ Ordered.ShiftLoopChainInv cfg pre.chain :=
  dryChainLenGridInv_preLoop_of_reached J hJn hJm hCap hReached.2.1 hGridInv hU hLenWithin hGrid
    hagree

/-- Helper: `Ordered.algorithm2_loopWith` preserves `DryChainLenGridInv J`. -/
theorem dryChainLenGridInv_loopWith (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    (κ : ℝ) (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ)
    (ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P)
    (branD : ℕ) (passes : Fin ((concreteCirculationCfgWithLast dryWitnessUsed J).P.d + 1) → ℕ)
    (lctOps : ℕ)
    (hLoopInv : Ordered.ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch)
    (hGridInv : DryChainLenGridInv J ch) :
    DryChainLenGridInv J (Ordered.algorithm2_loopWith
      (concreteCirculationCfgWithLast dryWitnessUsed J) κ extG e2i g' ℓ' ch branD passes lctOps).1 := by
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hV : cfg.ValidOrdNoHidden := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  change DryChainLenGridInv J (Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps).1
  rw [Ordered.algorithm2_loopWith]; dsimp only
  by_cases hGood : extG.inner g' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) /
      extG.lnorm ℓ' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) ≤ -(κ * cfg.α)
  · rw [dite_eq_left hGood]; exact hGridInv
  · rw [dite_eq_right hGood]
    cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
    | none => exact hGridInv
    | some i =>
      dsimp only
      by_cases hCapShift : (ch.shiftCount i.val : ℝ) + 1 ≤
          gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
      · rw [dite_eq_left hCapShift]
        exact dryChainLenGridInv_loopWith J hJn hJm hCap κ extG e2i g' ℓ' _ _ _ _
          (hLoopInv.shift hV i.val (Nat.lt_succ_iff.mp i.isLt))
          (dryChainLenGridInv_shift J hJn hJm hCap hLoopInv hGridInv (Nat.lt_succ_iff.mp i.isLt))
      · rw [dite_eq_right hCapShift]; exact hGridInv
termination_by shiftRemainingBudget (concreteCirculationCfgWithLast dryWitnessUsed J).P
    (alg2PsiGame (concreteCirculationCfgWithLast dryWitnessUsed J).Ψ
      (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀) ch
decreasing_by simpa using Chain.Ordered.shiftRemainingBudget_lt_of_step ch i hCapShift

/-- **`DryChainLenGridInv` is preserved across the full `Ordered.algorithm2_updateWith` operation.** -/
theorem dryChainLenGridInv_update (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {L : ℕ} {Rcore : DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T)}
    {κ : ℝ} {P_inv : ℕ}
    {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    {tok : SolverToken (concreteCirculationCfgWithLast dryWitnessUsed J) L Rcore}
    (hReached : OrdSolverReachedInv κ (namedInstance (solverConnectedAugmented J)) P_inv model tok)
    (hGridInv : DryChainLenGridInv J model.chain)
    {U_ext : List Update} {g_ext l_ext : ℕ → ℝ} {η : ℝ}
    (hU : RefreshBatch (namedInstance (solverConnectedAugmented J)) U_ext)
    (hLenWithin : IPM.LengthsWithin (namedInstance (solverConnectedAugmented J))
      (ipmQualityRangeExponent (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m)) l_ext)
    (hGrid : IsDyadicGrid (namedInstance (solverConnectedAugmented J))
      (ipmQualityPrecision (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m)) l_ext)
    (hagree : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      (∀ u ∈ U_ext, ¬ u.Inserts e) → g_ext e = model.extg e ∧ l_ext e = model.extℓ e) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    DryChainLenGridInv J (Ordered.algorithm2_updateWith cfg κ model U_ext g_ext l_ext η).1.chain := by
  intro cfg; dsimp only [Ordered.algorithm2_updateWith]
  split <;> exact dryChainLenGridInv_loopWith J hJn hJm hCap κ _ _ _ _ _ _ _ _
    (dryChainLenGridInv_preLoop_and_inv J hJn hJm hCap hReached hGridInv hU hLenWithin hGrid hagree).2
    (dryChainLenGridInv_preLoop_and_inv J hJn hJm hCap hReached hGridInv hU hLenWithin hGrid hagree).1
end MinCostFlow.Final.DryRun
end
