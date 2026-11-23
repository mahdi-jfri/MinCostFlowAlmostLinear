module

public import MinCostFlow.Final.AssemblyDryRunSCCoreLoopHelpers
import Mathlib.Tactic

/-!
# Dry-run `UpdateLoopModelInv` derivation (`AssemblyDryRunSCCoreLoopModel`)

Derives the full `UpdateLoopModelInv` (`MinRatio/WireChainSpecs.lean:428-516`) at the dry-run
parameters from the existing premises of `OrdChainUpdateCoreSpecWKFBLSel` together with the
rebuild-count word bound `∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- **Full dry-run `UpdateLoopModelInv` derivation:** derives every conjunct of `UpdateLoopModelInv`
at the dry values from the existing premises of `OrdChainUpdateCoreSpecWKFBLSel` together with the
rebuild-count word bound `∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w`. -/
theorem dryCoreSel_updateLoopModelInv
    (allocationCoefficient allocationDegree wordExp : ℕ)
    (hSCWordCoeff : Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize
      dryWitnessUsed) ≤ allocationCoefficient)
    (hWordExpLe : wordExp ≤ 39)
    (source J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap1 : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
    ∀ {model : Alg2State cfg} {U : List Update} {gVec lVec : ℕ → ℝ},
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let modelPre := alg2PreResetState cfg model U gVec lVec
      FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh →
      model.extG = G →
      (∀ ei ∈ (model.chain.G 0).E, model.chain.ℓ ei = model.extℓ (model.intToExt ei)) →
      Ordered.ShiftLoopChainInv cfg model.chain →
      Ordered.ShiftLoopChainInv cfg modelPre.chain →
      DryChainLenGridInv J model.chain →
      DryChainLenGridInv J modelPre.chain →
      RefreshBatch model.extG U →
      tr.2.2.2.1 ≤ initTargetCap cfg G →
      (∀ e ∈ model.extG.E, (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ lVec e ∧
        lVec e ≤ (2 : ℝ) ^ F.rangeExponent) →
      (∀ e ∈ model.extG.E, (∀ u ∈ U, ¬ u.Inserts e) → lVec e = model.extℓ e) →
      (∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w) →
      UpdateLoopModelInv w F.limbs F.fmt.precision wordExp (dryLastStretchP J)
        (fun _ => G.n) (fun _ => initTargetCap cfg G)
        (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j)
        (fun e' => lVec (tr.2.2.1 e')) (fun e' => gVec (tr.2.2.1 e')) cfg.P.d 0
        { model.chain with
          recUpdates := fun j =>
            if j = 0 then model.chain.recUpdates 0 + tr.2.2.2.2.length
            else model.chain.recUpdates j }
        ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.2.2.2
        ((model.chain.G 0).batchEnc tr.2.2.2.2) (model.chain.levelOrd 0) := by
  intro I V k F cfg G w model U gVec lVec tr modelPre
    hFresh hExtG hChℓ hShift0 hShift1 _hGrid0 hGrid1 hRef hnfCap hLRng hLAgree hRebW
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
  have hT : cfg.T = sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed
      (Expander.chosenL (cfg.P.M₀ ^ 2)) sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool dryWitnessUsed sparsifyImplUsed rfl rfl rfl J hw
  have hInitAll : ∀ b < cfg.P.k,
      IsValidLSFInitFor (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed cfg.P.k b :=
    fun b hb => dryLSFInitUsed_isValidLSFInitFor F.limbs F.fmt.precision cfg.P.k b hb
  have hStretchLe : dryLastStretchP J ≤ 100 * ipmQualityRangeExponent I.m V k :=
    dryLastStretchP_im_le_100_E J hJn hJm hCap1
  have hWordLvl : ∀ j < cfg.P.d,
      levelM cfg.TP cfg.P j < 2 ^ w ∧
      (levelM cfg.TP cfg.P j + cfg.N₀ + 2) ^ wordExp * (F.limbs + 1) < 2 ^ w := by
    intro j hj
    have hL := (concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm hCap1 j hj.le 0 0
      (by omega)).2
    have hSC := Classical.choose_spec
      (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed)
      allocationCoefficient allocationDegree hSCWordCoeff source J hJn hJm hCap1 hw
    refine ⟨?_, hSC wordExp hWordExpLe j F.limbs hL⟩
    have h1 := hSC 1 (by decide) j F.limbs hL
    rw [pow_one] at h1
    exact lt_of_le_of_lt
      (le_trans (show levelM cfg.TP cfg.P j ≤ levelM cfg.TP cfg.P j + cfg.N₀ + 2 by omega)
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))) h1
  set U_int := tr.2.2.2.2
  set G0' := (model.chain.G 0).applyBatch U_int
  set ℓ' := fun e' => lVec (tr.2.2.1 e')
  set g' := fun e' => gVec (tr.2.2.1 e')
  have hTr := translateBatch_preserves U model.extG (model.chain.G 0)
    model.extToInt model.intToExt model.nextFresh hFresh hRef.1
  dsimp only at hTr
  have hEdgeU : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    have hns := hRef.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact absurd hns id
  have hEdgeInt : ∀ u ∈ U_int, IsEdgeUpdate u :=
    translateBatch_isEdgeUpdate _ _ _ _ _ hEdgeU
  have hBatch0 : (model.chain.G 0).BatchIsValid U_int := hTr.2.2.1
  have hExtEq : tr.1 = model.extG := hTr.1.trans hRef.2.1
  have hG0'V : G0'.V = G.V := by rw [← hTr.2.1.hV, hExtEq, hExtG]
  have hG0'E_lt : ∀ e ∈ G0'.E, e < initTargetCap cfg G := fun e he =>
    lt_of_lt_of_le (hTr.2.1.hLtFresh e he) hnfCap
  have hG0'V_lt : ∀ x ∈ G0'.V, x < G.n := fun x hx => by
    rw [hG0'V] at hx
    simpa [G, namedInstance, MGraph.n] using hx
  have hℓ'Stable : ∀ e ∈ G0'.E, e ∈ (model.chain.G 0).E → (∀ u ∈ U_int, ¬ u.Inserts e) →
      ℓ' e = model.chain.ℓ e := by
    intro e heNew heOld _
    have hlt : e < model.nextFresh := hFresh.hLtFresh e heOld
    have hI2E : tr.2.2.1 e = model.intToExt e := hTr.2.2.2.2.2.2.2.1 e hlt
    have hExtMem : model.intToExt e ∈ model.extG.E := by
      rw [← hExtEq, ← hI2E]; exact (hTr.2.1.hRight e heNew).2
    have hNoInsExt : ∀ u ∈ U, ¬ u.Inserts (model.intToExt e) := by
      intro u hu hIns
      have hge : model.nextFresh ≤ tr.2.1 (model.intToExt e) :=
        hTr.2.2.2.2.2.2.2.2.2 (model.intToExt e) (hExtEq.symm ▸ hExtMem) ⟨u, hu, hIns⟩
      have heq : tr.2.1 (model.intToExt e) = e := by
        rw [← hI2E]; exact (hTr.2.1.hRight e heNew).1
      omega
    dsimp only [ℓ']
    rw [hI2E, hLAgree _ hExtMem hNoInsExt, hChℓ e heOld]
  have hU_int_len : U_int.length ≤ 3 * initTargetCap cfg G := by
    have hlenEq : U_int.length = U.length := by
      have hCount : ∀ (W : List Update) (Gcur : MGraph) (f g : ℕ → ℕ) (nf0 : ℕ),
          (∀ u ∈ W, IsEdgeUpdate u) → (translateBatch Gcur f g nf0 W).2.2.2.2.length = W.length := by
        intro W; induction W with
        | nil => intros; rfl
        | cons u rest ih =>
          intro Gcur f g nf0 hE
          have hu := hE u List.mem_cons_self
          have hr := fun x hx => hE x (List.mem_cons_of_mem _ hx)
          cases u with
          | insert _ _ _ => simpa [translateBatch] using ih _ _ _ _ hr
          | delete _ => simpa [translateBatch] using ih _ _ _ _ hr
          | split _ _ _ _ => simp [IsEdgeUpdate] at hu
      exact hCount U model.extG model.extToInt model.intToExt model.nextFresh hEdgeU
    rw [hlenEq]
    have hGmCap : model.extG.m ≤ initTargetCap cfg G := by
      rw [hExtG]; unfold initTargetCap; omega
    exact refreshBatch_length_le_three_mul hFresh hRef hGmCap hnfCap
  have hBatchCaps0 : BatchWithinCaps G.n (initTargetCap cfg G) U_int := by
    intro u hu
    have hE := hEdgeInt u hu
    cases u with
    | delete _ => trivial
    | insert e a b =>
      exact lt_of_lt_of_le (hTr.2.2.2.2.2.2.1 (.insert e a b) hu e rfl).2 hnfCap
    | split _ _ _ _ => simp [IsEdgeUpdate] at hE
  have hH0 := (hShift0.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hH1 := (hShift1.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hB1 := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hShift1.1
  have hOrd0 : OrderedBatch (model.chain.G 0) U_int (model.chain.levelOrd 0)
      (Chain.Ordered.chainLevelOrd cfg.T (fun j => if j = 0 then G0' else model.chain.G j)
        model.chain.scState model.chain.bran 0) :=
    ⟨sortedRotation (model.chain.G 0), sortedRotation G0', rfl,
      by simp [chainLevelOrd, sortedRotation],
      (sortedRotation_batch hBatch0 hEdgeInt).mono (Nat.zero_le 2)⟩
  -- Main induction on `rem = cfg.P.d - idx`
  have hMain : ∀ (rem idx : ℕ) (st : ChainState cfg.T cfg.P) (curG : MGraph)
      (curU : List Update) (curEncAcc : ℕ) (oldOrd : ℕ → List End),
      idx + rem = cfg.P.d →
      (∀ j, idx ≤ j → st.G j = model.chain.G j ∧ st.scState j = model.chain.scState j ∧
        st.updCount j = model.chain.updCount j) →
      (∀ j < idx, st.G j = modelPre.chain.G j ∧ st.scState j = modelPre.chain.scState j ∧
        st.updCount j = modelPre.chain.updCount j) →
      st.bran = model.chain.bran ∧ st.rebuildCount = model.chain.rebuildCount ∧
        st.lvlM = model.chain.lvlM ∧ st.N₀ = model.chain.N₀ →
      (Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem idx st curG curU curEncAcc).1 =
        modelPre.chain →
      (idx = 0 → curU.length ≤ 3 * initTargetCap cfg G) →
      (0 < idx → curU.length ≤ modelPre.chain.curFwd (idx - 1) ∧
        curG = cfg.T.S (st.scState (idx - 1)) (st.bran (idx - 1))) →
      curG = (st.G idx).applyBatch curU ∧ (st.G idx).BatchIsValid curU ∧ curG.E ⊆ G0'.E →
      (idx < cfg.P.d →
        BatchWithinCaps G.n (initTargetCap cfg G) curU ∧
        oldOrd = model.chain.levelOrd idx ∧
        OrderedBatch (st.G idx) curU oldOrd
          (Chain.Ordered.chainLevelOrd cfg.T (fun j => if j = idx then curG else st.G j)
            st.scState st.bran idx)) →
      (∀ e ∈ curG.E, e ∈ (model.chain.G idx).E → (∀ u ∈ curU, ¬ u.Inserts e) →
        ({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen
          ℓ' idx e = model.chain.toTreeChain.chainLen model.chain.ℓ idx e) →
      UpdateLoopModelInv w F.limbs F.fmt.precision wordExp (dryLastStretchP J)
        (fun _ => G.n) (fun _ => initTargetCap cfg G)
        (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) ℓ' g' rem idx st curG curU
        curEncAcc oldOrd := by
    intro rem
    induction rem with
    | zero =>
      intro idx st curG curU curEncAcc oldOrd hsum hGe hLt hEqF hEndEq _ hPos hCur _ _
      have hieq : idx = cfg.P.d := by omega
      subst hieq
      refine ⟨fun hnil => by rw [hCur.1, hnil]; rfl, fun hne => ?_⟩
      have hdPos : 0 < cfg.P.d := cfg.P.hd
      have hEndD := hEndEq
      dsimp only [Ordered.updateLoop] at hEndD
      simp only [hne, ↓reduceIte] at hEndD
      set Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = cfg.P.d then curG else st.G j }
      set ℓd := Cpartial.chainLen ℓ' cfg.P.d
      have hLastKEq : (cfg.L.build curG ℓd).1 = modelPre.chain.lastK := by rw [← hEndD]
      have hGDEq : curG = modelPre.chain.G cfg.P.d := by rw [← hEndD]; simp
      have hℓdEq : ℓd = modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ cfg.P.d := by
        rw [← hEndD]
        apply chainLen_congr_upto rfl cfg.P.d
        intro j hj
        simp only [TreeChain.activeLSF, ChainState.toTreeChain, Cpartial, hj, ↓reduceIte]
      have hPreD1 : SparseCoreOrdInput cfg.T cfg.P.k (st.lvlM (cfg.P.d - 1)) st.N₀
          (st.scState (cfg.P.d - 1)) (st.G (cfg.P.d - 1))
          (st.levelOrd (cfg.P.d - 1)) (st.updCount (cfg.P.d - 1)) := by
        have hIn := levelHistory_sparseCoreOrdInput
          (Classical.choice (hShift1.1.hHist (cfg.P.d - 1) (by omega)))
        have hStPre : st.G (cfg.P.d - 1) = modelPre.chain.G (cfg.P.d - 1) ∧
            st.scState (cfg.P.d - 1) = modelPre.chain.scState (cfg.P.d - 1) ∧
            st.updCount (cfg.P.d - 1) = modelPre.chain.updCount (cfg.P.d - 1) :=
          hLt (cfg.P.d - 1) (by omega)
        have hOrdEq : st.levelOrd (cfg.P.d - 1) = modelPre.chain.levelOrd (cfg.P.d - 1) := by
          rw [← hEndD]; unfold ChainState.levelOrd Ordered.chainLevelOrd
          by_cases h0 : cfg.P.d - 1 = 0
          · simp [h0, show (0 : ℕ) ≠ cfg.P.d by omega]
          · simp [h0]
        rw [hEqF.2.2.1, hEqF.2.2.2, hShift0.1.hLvlM, hShift0.1.hN0, hStPre.1, hStPre.2.1,
          hStPre.2.2, hOrdEq]
        exact hIn
      have hSubD1 : curG.E ⊆ (st.G (cfg.P.d - 1)).E := by
        rw [hGDEq, (hLt (cfg.P.d - 1) (by omega)).1]
        have h1 := chainInv_G_succ_E_subset hV hShift1.1 (by omega : cfg.P.d - 1 < cfg.P.d)
        rwa [Nat.sub_add_cancel hdPos] at h1
      refine ⟨hLastKEq ▸ hShift1.1.hLastK,
        drySC_lastLevelBuildEqOnE J curG _ ℓd (fun e he => ite_eq_left he),
        fun e he => by
          change 0 < ℓd e
          rw [hℓdEq]; exact lt_of_lt_of_le (by positivity)
            ((hGrid1.2.2.1 cfg.P.d le_rfl).1 e (hGDEq ▸ he)).1,
        fun e he => by
          change 2 * (2 : ℝ) ^ dryLastStretchP J * lastLevelStretchBound curG ℓd e < _
          rw [hGDEq, hℓdEq]
          exact dryChainLenGridInv_implies_lastStretchFits J hJn hJm hCap1 hShift1.1 hGrid1
            hStretchLe e (hGDEq ▸ he),
        fun _ => ⟨hPreD1, (hPos hdPos).2, hSubD1, fun e he => by
          change ∃ q : ℤ, Num.Fits 4 F.limbs q ∧ (q : ℝ) / (2 : ℝ) ^ F.fmt.precision = ℓd e
          rw [hℓdEq]
          have h1 := dryChainLenGridInv_implies_coreLenFits J hJn hJm hCap1 hGrid1
            (cfg.P.d - 1) (Nat.sub_lt hdPos Nat.zero_lt_one) e
            (by rw [Nat.sub_add_cancel hdPos]; exact hGDEq ▸ he)
          rwa [Nat.sub_add_cancel hdPos] at h1⟩⟩
    | succ rem' ih =>
      intro idx st curG curU curEncAcc oldOrd hsum hGe hLt hEqF hEndEq hLen0 hPos hCur hLtD hLenStab
      have hidxLt : idx < cfg.P.d := by omega
      have hUpdW : st.updCount idx + curU.length < 2 ^ w := by
        rw [(hGe idx le_rfl).2.2]
        exact dryCoreSel_updCount_add_curU_lt_two_pow_wordSize allocationCoefficient
          allocationDegree hSCWordCoeff source J hJn hJm hCap1 hw hidxLt hShift0.1 hShift1.1
          hLen0 (fun hp => (hPos hp).1)
      obtain ⟨hBCaps, hOldOrdEq, hOrdCur⟩ := hLtD hidxLt
      refine ⟨hUpdW, hCur.2.1, hBCaps, hCur.1, fun e he => hG0'E_lt e (hCur.2.2 he), ?_⟩
      by_cases hOver : intRebuildThreshold cfg.P st.N₀ idx < st.updCount idx + curU.length
      · simp only [hOver, ↓reduceIte]
        have hOverN0 : intRebuildThreshold cfg.P cfg.N₀ idx < st.updCount idx + curU.length := by
          rwa [hEqF.2.2.2, hShift0.1.hN0] at hOver
        have hEndReb :
            (Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
              { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
              idx (rebuildStartGraph idx curG) curEncAcc).1 = modelPre.chain := by
          dsimp only [Ordered.updateLoop] at hEndEq
          simpa [hOverN0] using hEndEq
        have hRebIdxW : st.rebuildCount idx + 1 < 2 ^ w := by
          rw [congrFun hEqF.2.1 idx]; exact hRebW idx hidxLt
        refine ⟨updateRebuildModelInv_of_end J hJn hJm hCap1 hw hWordLvl hStretchLe hRebIdxW
            (by dsimp only; rw [hEndReb]; exact hShift1.1)
            (by dsimp only; rw [hEndReb]; exact hGrid1), fun hidxPos => ?_⟩
        have hIn := levelHistory_sparseCoreOrdInput
          (Classical.choice (hShift1.1.hHist (idx - 1) (by omega)))
        have hStPre := hLt (idx - 1) (by omega)
        have hOrdEq : st.levelOrd (idx - 1) = modelPre.chain.levelOrd (idx - 1) := by
          obtain ⟨_, _, hAgr⟩ := updateLoop_prefix_agrees_end cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g'
            (rem' + 1) idx st curG curU curEncAcc hsum hidxPos
          rw [hEndEq] at hAgr
          unfold ChainState.levelOrd Ordered.chainLevelOrd
          by_cases h0 : idx - 1 = 0
          · simp [h0, (hAgr 0 hidxPos).1]
          · simp [h0, (hAgr (idx - 1 - 1) (by omega)).2.1, (hAgr (idx - 1 - 1) (by omega)).2.2.1]
        rw [hEqF.2.2.1, hEqF.2.2.2, hShift0.1.hLvlM, hShift0.1.hN0, hStPre.1, hStPre.2.1,
          hStPre.2.2, hOrdEq]
        exact hIn
      · simp only [hOver, ↓reduceIte]
        have hNotOverN0 : ¬ intRebuildThreshold cfg.P cfg.N₀ idx < st.updCount idx + curU.length := by
          rwa [hEqF.2.2.2, hShift0.1.hN0] at hOver
        set Cpartial : TreeChain :=
          { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
        set ℓi := Cpartial.chainLen ℓ' idx
        set gi := Cpartial.chainGrad g' idx
        set ordNew := Chain.Ordered.chainLevelOrd cfg.T
          (fun j => if j = idx then curG else st.G j) st.scState st.bran idx
        set updRes := cfg.T.updateOrd (st.scState idx) curU ℓi gi ordNew
        set sc' := updRes.1
        set nextG := cfg.T.S sc' (st.bran idx)
        set nextU := updRes.2 (st.bran idx)
        set nextEnc := (st.G (idx + 1)).batchEnc nextU
        set fiChanges := diffTreeChanges (cfg.T.lsfs (st.scState idx) (st.bran idx)).F.F.E
          (cfg.T.lsfs sc' (st.bran idx)).F.F.E
        set stNext : ChainState cfg.T cfg.P :=
          { st with
            G := fun j => if j = idx then curG else st.G j
            scState := fun j => if j = idx then sc' else st.scState j
            updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
            recUpdates := fun j =>
              if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
            curFwd := fun j =>
              if j = idx then st.curFwd idx + nextU.length else st.curFwd j
            curEnc := fun j =>
              if j = idx then st.curEnc idx + curEncAcc
              else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
              else st.curEnc j
            curDecUpdates := fun j =>
              if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j }
        have hEndNext :
            (Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem' (idx + 1)
              stNext nextG nextU 0).1 = modelPre.chain := by
          dsimp only [Ordered.updateLoop] at hEndEq
          simpa [hNotOverN0, Cpartial, ℓi, gi, ordNew, updRes, sc', nextG, nextU, nextEnc,
            fiChanges, stNext] using hEndEq
        obtain ⟨hℓEnd, hGNextEnd, hPreNextEnd⟩ := updateLoop_prefix_agrees_end cfg.T cfg.L cfg.TP
          cfg.P cfg.N₀ ℓ' g' rem' (idx + 1) stNext nextG nextU 0 (by omega) (Nat.succ_pos idx)
        rw [hEndNext] at hℓEnd hGNextEnd hPreNextEnd
        have hIdxEnd := hPreNextEnd idx (Nat.lt_succ_self idx)
        have hEndGidx : modelPre.chain.G idx = curG := by simpa [stNext] using hIdxEnd.1
        have hEndScidx : modelPre.chain.scState idx = sc' := by simpa [stNext] using hIdxEnd.2.1
        have hEndBridx : modelPre.chain.bran idx = model.chain.bran idx := by
          rw [hIdxEnd.2.2.1]; exact congrFun hEqF.1 idx
        have hEndFwdidx : modelPre.chain.curFwd idx = st.curFwd idx + nextU.length := by
          simpa [stNext] using hIdxEnd.2.2.2.2
        have hOrdNewEqEnd : ordNew = modelPre.chain.levelOrd idx := by
          unfold ordNew ChainState.levelOrd Ordered.chainLevelOrd
          by_cases h0 : idx = 0
          · subst h0; simp [hEndGidx]
          · have hpm := hPreNextEnd (idx - 1) (by omega)
            have hne : idx - 1 ≠ idx := by omega
            have hScP : modelPre.chain.scState (idx - 1) = st.scState (idx - 1) := by
              simpa [stNext, hne] using hpm.2.1
            have hBrP : modelPre.chain.bran (idx - 1) = st.bran (idx - 1) := hpm.2.2.1
            simp [h0, hScP, hBrP]
        -- Transport `progTool_updateOrd_step_facts` across `hT`
        have hStepFacts :
            nextG = (model.chain.G (idx + 1)).applyBatch nextU ∧
            (model.chain.G (idx + 1)).BatchIsValid nextU ∧
            (∀ u ∈ nextU, match u with | .insert e _ _ => e ∈ nextG.E | _ => True) ∧
            (∀ vCap eCap, (∀ x ∈ nextG.V, x < vCap) → (∀ e ∈ nextG.E, e < eCap) →
              BatchWithinCaps vCap eCap nextU) ∧
            OrderedBatch (model.chain.G (idx + 1)) nextU
              (cfg.T.rot (model.chain.scState idx) (model.chain.bran idx))
              (cfg.T.rot sc' (model.chain.bran idx)) ∧
            (∀ e ∈ nextG.E, (∀ u ∈ nextU, ¬ u.Inserts e) →
              e ∈ (model.chain.G (idx + 1)).E ∧
              (∀ u ∈ curU, ¬ u.Inserts e) ∧
              (cfg.T.lsfs sc' (model.chain.bran idx)).wstr e =
                (cfg.T.lsfs (model.chain.scState idx) (model.chain.bran idx)).wstr e) := by
          have hGkEq : modelPre.chain.G idx = (model.chain.G idx).applyBatch curU := by
            rw [hEndGidx, hCur.1, (hGe idx le_rfl).1]
          have hBk0 : (model.chain.G idx).BatchIsValid curU := (hGe idx le_rfl).1 ▸ hCur.2.1
          have hOrdK0 : OrderedBatch (model.chain.G idx) curU (model.chain.levelOrd idx) ordNew := by
            rwa [(hGe idx le_rfl).1, hOldOrdEq] at hOrdCur
          have hScEq0 : modelPre.chain.scState idx =
              (cfg.T.updateOrd (model.chain.scState idx) curU ℓi gi ordNew).1 := by
            rw [hEndScidx]; dsimp only [sc', updRes]; rw [(hGe idx le_rfl).2.1]
          have hGk1New : modelPre.chain.G (idx + 1) =
              cfg.T.S (modelPre.chain.scState idx) (model.chain.bran idx) := by
            rw [hGNextEnd, hEndScidx]; dsimp only [nextG]; rw [congrFun hEqF.1 idx]
          have hCast := progTool_updateOrd_step_facts_eq hT hShift0.1 hShift1.1 hH0 hH1
            hInitAll hidxLt hGkEq hBk0 hOrdK0 hScEq0 hEndBridx hGk1New hOrdNewEqEnd
          dsimp only at hCast
          have hSc0Eq : st.scState idx = model.chain.scState idx := (hGe idx le_rfl).2.1
          have hBr0Eq : st.bran idx = model.chain.bran idx := congrFun hEqF.1 idx
          have hSc'Eq : sc' = (cfg.T.updateOrd (model.chain.scState idx) curU ℓi gi ordNew).1 := by
            dsimp only [sc', updRes]; rw [hSc0Eq]
          have hNextGEq : nextG = cfg.T.S sc' (model.chain.bran idx) := by
            dsimp only [nextG]; rw [hBr0Eq]
          have hNextUEq : nextU = (cfg.T.updateOrd (model.chain.scState idx) curU ℓi gi ordNew).2
              (model.chain.bran idx) := by
            dsimp only [nextU, updRes]; rw [hSc0Eq, hBr0Eq]
          rw [hNextGEq, hNextUEq, hSc'Eq]
          exact ⟨hCast.1, hCast.2.1, fun u hu => by
            have := hCast.2.2.1 u hu; cases u <;> exact this,
            hCast.2.2.2.1, hCast.2.2.2.2.1, hCast.2.2.2.2.2⟩
        have hCostMono : cfg.T.cost (st.scState idx) ≤ cfg.T.cost sc' :=
          progTool_updateOrd_cost_mono_eq hT (st.scState idx) curU ℓi gi ordNew
        have hℓiEqEnd : ℓi = modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ idx := by
          apply chainLen_congr_upto hℓEnd.symm idx
          intro j hj
          have hpm := hPreNextEnd j (Nat.lt_succ_of_lt hj)
          have hne : j ≠ idx := Nat.ne_of_lt hj
          have hjd : j < cfg.P.d := lt_trans hj hidxLt
          simp only [TreeChain.activeLSF, ChainState.toTreeChain, Cpartial, hjd, ↓reduceIte]
          rw [show modelPre.chain.scState j = st.scState j by simpa [stNext, hne] using hpm.2.1,
            hpm.2.2.1]
        have hCoreLenEqEnd :
            coreLen (cfg.T.lsfs sc' (st.bran idx)) ℓi =
              modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (idx + 1) := by
          rw [hℓiEqEnd]
          change coreLen (cfg.T.lsfs sc' (st.bran idx)) _ =
            coreLen (modelPre.chain.toTreeChain.activeLSF idx) _
          have hact : modelPre.chain.toTreeChain.activeLSF idx = cfg.T.lsfs sc' (st.bran idx) := by
            simp only [TreeChain.activeLSF, ChainState.toTreeChain, hidxLt, ↓reduceIte,
              hEndScidx, hIdxEnd.2.2.1]
            rfl
          rw [hact]
        have hNextSubCur : nextG.E ⊆ curG.E := by
          rw [← hGNextEnd, ← hEndGidx]
          exact chainInv_G_succ_E_subset hV hShift1.1 hidxLt
        have hNextSubG0' : nextG.E ⊆ G0'.E := hNextSubCur.trans hCur.2.2
        have hNextV_lt : ∀ x ∈ nextG.V, x < G.n := by
          intro x hx
          have hEndG0 : modelPre.chain.G 0 = G0' := by
            rcases algorithm1_update_G0_and_g cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
                U_int g' ℓ' with ⟨hf0, _, _⟩ | ⟨_, hG0e, _⟩
            · exfalso
              have hrc0 : modelPre.chain.rebuildCount 0 = model.chain.rebuildCount 0 := by
                have hrc := Ordered.updateLoop_rebuildCount_cases cfg.T cfg.L cfg.TP cfg.P
                  cfg.N₀ ℓ' g' rem' (idx + 1) stNext nextG nextU 0 (by omega)
                rcases hrc with heq | ⟨iStar, hi1, _, heq⟩
                · rw [← hEndNext, heq]; exact congrFun hEqF.2.1 0
                · rw [← hEndNext, heq]; simp [show (0 : ℕ) ≠ iStar by omega]
                  exact congrFun hEqF.2.1 0
              have hne0 : model.chain.rebuildCount 0 < modelPre.chain.rebuildCount 0 :=
                (firstRebuiltLevel_eq_some_zero_iff cfg.P.hd _ _).mp hf0
              omega
            · exact hG0e
          have hx0 : x ∈ (modelPre.chain.G 0).V := (hB1 (idx + 1) hidxLt).2.1 (hGNextEnd ▸ hx)
          exact hG0'V_lt x (hEndG0 ▸ hx0)
        have hNextBCaps : BatchWithinCaps G.n (initTargetCap cfg G) nextU :=
          hStepFacts.2.2.2.1 G.n (initTargetCap cfg G) hNextV_lt
            (fun e he => hG0'E_lt e (hNextSubG0' he))
        have hScIn : SparseCoreOrdInput cfg.T cfg.P.k (st.lvlM idx) st.N₀
            (st.scState idx) (st.G idx) oldOrd (st.updCount idx) := by
          have hIn := levelHistory_sparseCoreOrdInput (Classical.choice (hShift0.1.hHist idx hidxLt))
          rw [hEqF.2.2.1, hEqF.2.2.2, hShift0.1.hLvlM, hShift0.1.hN0,
            (hGe idx le_rfl).1, (hGe idx le_rfl).2.1, (hGe idx le_rfl).2.2, hOldOrdEq]
          exact hIn
        have hLeThr : ((st.updCount idx + curU.length : ℕ) : ℝ) ≤
            SparseCoreTool.updateThreshold cfg.P.k (st.lvlM idx) st.N₀ := by
          rw [hEqF.2.2.1, hEqF.2.2.2, hShift0.1.hLvlM, hShift0.1.hN0]
          exact (Nat.cast_le.mpr (Nat.le_of_not_lt hNotOverN0)).trans
            (intRebuildThreshold_le_updateThreshold hV.hTP cfg.N₀ idx)
        refine ⟨hScIn, hOrdCur, hLeThr, hCostMono,
          fun e he => by
            rw [hℓiEqEnd]
            exact lt_of_lt_of_le (by positivity)
              ((hGrid1.2.2.1 idx hidxLt.le).1 e (hEndGidx ▸ he)).1,
          fun hidx1Lt => ⟨by rw [(hGe (idx + 1) (by omega)).1, (hGe idx le_rfl).2.1,
              congrFun hEqF.1 idx]; exact hShift0.1.hGSucc idx hidxLt,
            (fun u hu => by
              have hIns := hStepFacts.2.2.1 u hu
              cases u with
              | delete _ => trivial
              | split _ _ _ _ => trivial
              | insert e a b =>
                have heNext : e ∈ nextG.E := hIns
                refine ⟨hNextSubCur heNext, hG0'E_lt e (hNextSubG0' heNext),
                  hG0'E_lt e (hNextSubG0' heNext), ?_⟩
                rw [hCoreLenEqEnd]
                exact dryChainLenGridInv_implies_coreLenFits J hJn hJm hCap1 hGrid1 idx hidxLt e
                  (hGNextEnd.symm ▸ heNext)),
            fun e he hNoNext => by
              obtain ⟨heOld, hNoCur, hWstrEq⟩ := hStepFacts.2.2.2.2.2 e he hNoNext
              refine ⟨(hGe (idx + 1) (by omega)).1.symm ▸ heOld, ?_⟩
              have heOldIdx : e ∈ (model.chain.G idx).E :=
                (Finset.mem_sdiff.mp (model.chain.toTreeChain.G_succ_E_subset hH0 hidxLt heOld)).1
              have hLenEq : ℓi e = model.chain.toTreeChain.chainLen model.chain.ℓ idx e :=
                hLenStab e (hNextSubCur he) heOldIdx hNoCur
              change (cfg.T.lsfs sc' (st.bran idx)).wstr e * ℓi e =
                coreLen (model.chain.toTreeChain.activeLSF idx)
                  (model.chain.toTreeChain.chainLen model.chain.ℓ idx) e
              simp only [coreLen, TreeChain.activeLSF, ChainState.toTreeChain, hidxLt, ↓reduceIte]
              rw [congrFun hEqF.1 idx, hWstrEq, hLenEq]
              rfl⟩, ?_⟩
        -- Inductive step to `rem', idx + 1`
        refine ih (idx + 1) stNext nextG nextU 0 (cfg.T.rot (st.scState idx) (st.bran idx))
          (by omega)
          (fun j hj => by
            have hne : j ≠ idx := by omega
            simpa [stNext, hne] using hGe j (by omega))
          (fun j hj => by
            by_cases hjeq : j = idx
            · rw [hjeq]
              have hIdxE := hPreNextEnd idx (Nat.lt_succ_self idx)
              exact ⟨hIdxE.1.symm, hIdxE.2.1.symm, hIdxE.2.2.2.1.symm⟩
            · have hne : j ≠ idx := hjeq
              simpa [stNext, hne] using hLt j (by omega))
          hEqF hEndNext (fun h => absurd h (Nat.succ_ne_zero idx))
          (fun _ => ⟨by simp only [Nat.add_sub_cancel]; rw [hEndFwdidx]; omega,
            by simp [stNext, nextG]⟩)
          ⟨by simpa [stNext, show idx + 1 ≠ idx by omega, (hGe (idx + 1) (by omega)).1] using
              hStepFacts.1,
           by simpa [stNext, show idx + 1 ≠ idx by omega, (hGe (idx + 1) (by omega)).1] using
              hStepFacts.2.1,
           hNextSubG0'⟩
          (fun hidx1Lt => by
            refine ⟨hNextBCaps, ?_, ?_⟩
            · unfold ChainState.levelOrd Ordered.chainLevelOrd
              simp [(hGe idx le_rfl).2.1, congrFun hEqF.1 idx]
            · have hOrdNext : OrderedBatch (stNext.G (idx + 1)) nextU
                  (cfg.T.rot (st.scState idx) (st.bran idx)) (cfg.T.rot sc' (st.bran idx)) := by
                simpa [stNext, show idx + 1 ≠ idx by omega, (hGe (idx + 1) (by omega)).1,
                  (hGe idx le_rfl).2.1, congrFun hEqF.1 idx] using hStepFacts.2.2.2.2.1
              have hEqOrd : Chain.Ordered.chainLevelOrd cfg.T
                  (fun j => if j = idx + 1 then nextG else stNext.G j) stNext.scState stNext.bran
                  (idx + 1) = cfg.T.rot sc' (st.bran idx) := by
                unfold Ordered.chainLevelOrd; simp [stNext]
              rwa [hEqOrd])
          (fun e he heOld hNoNext => by
            obtain ⟨_, hNoCur, hWstrEq⟩ := hStepFacts.2.2.2.2.2 e he hNoNext
            have heOldIdx : e ∈ (model.chain.G idx).E :=
              (Finset.mem_sdiff.mp (model.chain.toTreeChain.G_succ_E_subset hH0 hidxLt heOld)).1
            have hCLpre :
                ({ stNext.toTreeChain with G := fun j => if j = idx + 1 then nextG else stNext.G j } :
                  TreeChain).chainLen ℓ' idx = ℓi := by
              apply chainLen_congr_upto rfl idx
              intro j hj
              have hne : j ≠ idx := Nat.ne_of_lt hj
              have hjd : j < cfg.P.d := lt_trans hj hidxLt
              simp [TreeChain.activeLSF, ChainState.toTreeChain, Cpartial, stNext, hjd, hne]
            have hCLstep :
                ({ stNext.toTreeChain with G := fun j => if j = idx + 1 then nextG else stNext.G j } :
                  TreeChain).chainLen ℓ' (idx + 1) e =
                (cfg.T.lsfs sc' (st.bran idx)).wstr e * ℓi e := by
              change coreLen _ _ e = _
              rw [hCLpre]
              simp [coreLen, TreeChain.activeLSF, ChainState.toTreeChain, stNext, hidxLt]
            rw [hCLstep, congrFun hEqF.1 idx, hWstrEq, hLenStab e (hNextSubCur he) heOldIdx hNoCur]
            simp [TreeChain.chainLen, coreLen, TreeChain.activeLSF, ChainState.toTreeChain, hidxLt])
  exact hMain cfg.P.d 0
    { model.chain with
      recUpdates := fun j =>
        if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
    G0' U_int ((model.chain.G 0).batchEnc U_int) (model.chain.levelOrd 0)
    (Nat.zero_add _) (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ h => absurd h (Nat.not_lt_zero _))
    ⟨rfl, rfl, rfl, rfl⟩ rfl (fun _ => hU_int_len) (fun h => absurd h (lt_irrefl 0))
    ⟨rfl, hBatch0, Finset.Subset.refl _⟩ (fun _ => ⟨hBatchCaps0, rfl, hOrd0⟩)
    (fun e heNew heOld hNo => by
      simpa [TreeChain.chainLen] using hℓ'Stable e heNew heOld hNo)

end MinCostFlow.Final.DryRun
