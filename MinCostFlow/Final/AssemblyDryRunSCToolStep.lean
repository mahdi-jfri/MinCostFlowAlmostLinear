module

public import MinCostFlow.Final.AssemblyDryRunSCToolStepUS
public import MinCostFlow.Final.AssemblyDryRunSCToolStepTerms
public import MinCostFlow.Final.AssemblyDryRunSCInnerSizes
public import MinCostFlow.MinRatio.WireChainCoreBranchBSizesKFBL
public import MinCostFlow.MinRatio.WireSelectFwdCost
import MinCostFlow.SparseCore.Program.AssemblyModel
import Mathlib.Tactic

/-!
# Dry-run proof of `BranchBToolStepKFBL` (`AssemblyDryRunSCToolStep`)

Combines all six terms of `stepBundleTree_machCost` (`branchStepCharge`):
- Term 1 (`U.length ≤ b`),
- Term 2 (`stepBundleTree_bunEnc_sum_le`),
- Term 3 (`stepBundleTreeMach_US_batchEnc_le`),
- Term 4 (`stepBundleTreeMach_dynMach_sum_le`),
- Term 5 (`lsfBatchSize_le`),
- Term 6 (`stepBundleTreeMach_lazyMach_sum_le`),

together with the forwarded-batch bounds from `MinRatio/WireSelectFwdCost.lean`
(`progTool_updateOrd_batchEnc_le_cost_sub`, `progTool_updateOrd_fwd_length_le_cost_sub`,
`progTool_shiftLoop_bran_lt_k`), to prove:

* `dryTool_updateOrd_cost_sub_le`: for any circulation `J` (`hJn`, `hJm`, `hCapPos`), any chain
  state `ch` meeting `ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch`,
  any level `j < cfg.P.d`, and any batch `U` meeting `BranchBStepBatchOK cfg ch j U` with
  `U.length ≤ b`,
  `cfg.T.cost (cfg.T.updateOrd (ch.scState j) U ℓ g ord').1 - cfg.T.cost (ch.scState j) ≤ dryInnerCoreStepCap J j b`.
* `dryTool_branchBToolStepKFBL`: full `BranchBToolStepKFBL cfg (dryInnerCoreStepCap J) ch`
  under `ShiftLoopChainInv cfg ch`.
-/

public section

namespace MinCostFlow.Final.DryRun

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.SparseCore MinCostFlow.SparseCore.Program MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program MinCostFlow.Bundle MinCostFlow.Scaling MinCostFlow.MinRatio
open MinCostFlow.IPM MinCostFlow.IPM.Machine

/-- Single-step tool cost bound for `concreteCirculationCfgWithLast dryWitnessUsed J`:
on any chain meeting `ShiftLoopChainInv`, any level `j < cfg.P.d`, and any valid batch `U`
satisfying `BranchBStepBatchOK cfg ch j U` with `U.length ≤ b`, updating the sparse-core tool
increases `cfg.T.cost` by at most `dryInnerCoreStepCap J j b`. -/
theorem dryTool_updateOrd_cost_sub_le (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hInv : ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch)
    {j : ℕ} (hj : j < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End)
    (hOK : BranchBStepBatchOK (concreteCirculationCfgWithLast dryWitnessUsed J) ch j U)
    {b : ℕ} (hb : U.length ≤ b) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    cfg.T.cost (cfg.T.updateOrd (ch.scState j) U ℓ g ord').1 - cfg.T.cost (ch.scState j) ≤
      dryInnerCoreStepCap J j b := by
  classical
  intro cfg
  let W := dryWitnessUsed
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let M₀ := max I.m threshold
  let kCap := cappedQualityExponent threshold A I.m
  let L_in := ipmQualityLimbs I.m V kCap
  let P_fp := ipmQualityPrecision I.m V kCap
  let lsfInit := W.lsfInit L_in P_fp
  let L := Expander.chosenL (cfg.P.M₀ ^ 2)
  let M := levelM cfg.TP cfg.P j
  let N := cfg.N₀
  let k := cfg.P.k
  let B_j := bundleLogFactor M N
  let Γ : ℕ := ⌈cfg.TP.γ_r (cfg.P.M₀ ^ 2)⌉₊
  have hV : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCapPos
  have hMsq : M ≤ cfg.P.M₀ ^ 2 := levelM_le_sq hV.hTP hV.hγM₀ hV.hγk j
  have hk1 : 1 ≤ k := Nat.succ_le_of_lt cfg.P.hk
  have hL1 : 1 ≤ L := Expander.one_le_chosenL (cfg.P.M₀ ^ 2)
  obtain ⟨H⟩ := hInv.1.hHist j hj
  let st : SparseCoreBundleState L := ch.scState j
  have hst_run : st = (sparseCoreBundleRestartToolMachWith lsfInit W.C_lsst L
      (fun _ => W.sparsify) W.params W.spanConst).runOrdAfterRestarts
      k M N H.D H.ord H.restarts H.len := H.hRun
  by_cases hV₀ : (H.D.G 0).V.Nonempty
  · have hNM_full := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit W.C_lsst L
      (fun _ => W.sparsify) W.params W.spanConst k M N H.D H.ord H.restarts H.len).2.2
    have hne_b : ((sparseCoreBundleRestartToolWith lsfInit W.C_lsst L
        (fun _ => W.sparsify)).runOrdAfterRestarts k M N H.D H.ord H.restarts H.len).isNonempty = true :=
      (runOrdAfterRestarts_isNonempty lsfInit W.C_lsst L (fun _ => W.sparsify)
        k M N H.D H.ord H.restarts H.len).2.1.trans (decide_eq_true hV₀)
    have hne : st.isNonempty = true := by
      rw [hst_run, hNM_full.isNonempty]; exact hne_b
    have hst_k : st.k = k := by
      rw [hst_run]
      exact (progTool_runOrdAfterRestarts_k_eq (lsfInit := lsfInit) (C_lsst := W.C_lsst)
        (depth := L) (impl := sparsifyImplUsed) k M N H.D H.ord H.restarts H.len)
    have hcost_eq := asm_update_cost_eq lsfInit W.C_lsst L (fun _ => W.sparsify) W.params
      W.spanConst st hne U ℓ g ord'
    have hsub_eq : cfg.T.cost (cfg.T.updateOrd st U ℓ g ord').1 - cfg.T.cost st =
        (Finset.range k).sum fun r =>
          branchStepCharge (fun _ => W.sparsify) (st.trees r) U st.ord ord' := by
      change (sparseCoreBundleRestartToolMachWith lsfInit W.C_lsst L (fun _ => W.sparsify)
          W.params W.spanConst).cost
          ((sparseCoreBundleRestartToolMachWith lsfInit W.C_lsst L (fun _ => W.sparsify)
            W.params W.spanConst).updateOrd st U ℓ g ord').1 -
          (sparseCoreBundleRestartToolMachWith lsfInit W.C_lsst L (fun _ => W.sparsify)
            W.params W.spanConst).cost st = _
      rw [hcost_eq, Nat.add_sub_cancel_left, hst_k]
    rw [show cfg.T.cost (cfg.T.updateOrd (ch.scState j) U ℓ g ord').1 - cfg.T.cost (ch.scState j) =
      cfg.T.cost (cfg.T.updateOrd st U ℓ g ord').1 - cfg.T.cost st from rfl, hsub_eq]
    have hℓ₀ : ∀ e ∈ (H.D.G 0).E, 0 < H.D.ℓ 0 e := H.hℓPos 0 (Nat.zero_le _)
    have hbranch : ∀ r ∈ Finset.range k,
        branchStepCharge (fun _ => W.sparsify) (st.trees r) U st.ord ord' ≤
          B_j * (10 + 112 * B_j) * (dryStepCapS J j + b) := by
      intro r hr
      have hr_lt : r < k := Finset.mem_range.mp hr
      have hInit_r : IsValidLSFInitFor lsfInit W.C_lsst k r := (W.hInit L_in P_fp).validFor hr_lt
      set Tm := sparseCoreBundleRestartToolMachWith lsfInit W.C_lsst L
        (fun _ => W.sparsify) W.params W.spanConst
      set Tb := sparseCoreBundleRestartToolWith lsfInit W.C_lsst L (fun _ => W.sparsify)
      set tr := (Tm.runOrdAfterRestarts k M N H.D H.ord H.restarts H.len).trees r
      set trb := (Tb.runOrdAfterRestarts k M N H.D H.ord H.restarts H.len).trees r
      have htr_eq : st.trees r = tr := by rw [hst_run]
      have hNM_r := hNM_full.trees r
      have hStepNM := BundleNonMachEq.step (fun _ => W.sparsify) hNM_r U st.ord ord'
      have hParams := (runOrdAfterRestartsMachWith_params lsfInit W.C_lsst L (fun _ => W.sparsify)
        W.params W.spanConst k M N H.D H.ord H.restarts H.len r).2
      have hBun := runOrdAfterRestarts_bun_inv lsfInit W.C_lsst L (fun _ => W.sparsify)
        k M N H.len hk1 H.D H.ord H.restarts H.hG0 hV₀ hℓ₀ H.hD H.hOrd r hInit_r H.len le_rfl
      have hbf := (foldl_bundleRestart_props lsfInit W.C_lsst L (fun _ => W.sparsify)
        (Tb.runOrdAfterUpdate k M N H.D H.ord H.restarts H.len).1 (H.restarts H.len)).2.2.2.2.1 r
      have hcs_eq_b : trb.cs =
          ((Tb.runOrdAfterUpdate k M N H.D H.ord H.restarts H.len).1.trees r).cs := hbf.cs
      have hG_eq : tr.cs.G = ch.G j := by
        rw [hNM_r.cs, hcs_eq_b, hBun.2.2.2.2.2.2.2.2.1, H.hEndG]
      have hBU : tr.cs.G.BatchIsValid U := hG_eq.symm ▸ hOK.2.1
      have hGm : tr.cs.G.m ≤ M := hG_eq.symm ▸ hOK.2.2
      have hI : CompLSFInv W.C_lsst (H.D.ℓ 0) tr.cs := by
        rw [hNM_r.cs, hcs_eq_b]; exact hBun.2.2.2.2.2.2.2.1
      -- Term 1: `U.length ≤ b`
      have hT1 : U.length ≤ b := hb
      -- Term 2: bundle batch encodings
      have hT2 : ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').state.activeComps.sum
          fun C => (tr.activeBuckets C).sum fun bkt =>
            (tr.dyn (C, bkt)).G.batchEnc
              ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').U_B (C, bkt))) ≤
          3 * (k + 1) * M := by
        rw [hStepNM.1.activeComps, hNM_r.activeBuckets, hNM_r.dyn, hStepNM.2.1]
        exact stepBundleTree_bunEnc_sum_le lsfInit W.C_lsst L hL1 (W.params M) (fun _ => W.sparsify)
          k M N H.len hk1 H.D H.ord H.restarts H.hInitMBound H.hInitNBound (W.hsparsify M)
          H.hG0 hV₀ hℓ₀ H.hD H.hOrd H.len r le_rfl hInit_r U st.ord ord'
      -- Term 3: `tr.S_cur.batchEnc info.U_S`
      have hT3 : tr.S_cur.batchEnc (stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').U_S ≤
          (5 + 24 * B_j) * M + (1 + 112 * B_j) * b :=
        stepBundleTreeMach_US_batchEnc_le lsfInit W.C_lsst L hL1 (W.params M) (fun _ => W.sparsify)
          W.params W.spanConst k M N H.len hk1 H.D H.ord H.restarts H.hInitMBound H.hInitNBound
          (W.hsparsify M) H.hG0 hV₀ hℓ₀ H.hD H.hOrd H.len r le_rfl hInit_r st.ord ord' hBU hGm hb
      -- Term 4: `∑ spanBatchChargeWith`
      have hT4 : ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').state.activeComps.sum
          fun C => (tr.activeBuckets C).sum fun bkt =>
            spanBatchChargeWith tr.spanConst tr.spanParams L
              ((tr.initBunG (C, bkt)).n + tr.splitBound) (tr.initBunG (C, bkt))
              (tr.dyn (C, bkt)).G
              ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').U_B (C, bkt))) ≤
          1080 * W.spanConst * Γ ^ 2 * (k + 1) ^ 2 * (115 * M + 4) * M :=
        stepBundleTreeMach_dynMach_sum_le lsfInit W.C_lsst (fun _ => W.sparsify) W.params
          W.hp_s W.hp_t cfg.P.M₀
          (concreteBucketCapacity true W.C_lsst cfg.Ψ cfg.P.M₀ cfg.N₀
            ((by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two W).trans (le_max_right _ _))))
          W.spanConst W.hspanConst k M N H.len hk1 hMsq H.D H.ord H.restarts
          H.hInitMBound H.hInitNBound (W.hsparsify M) H.hG0 hV₀ hℓ₀ H.hD H.hOrd H.len r le_rfl
          hInit_r U st.ord ord'
      -- Term 5: `lsfBatchSize tr.cs U ≤ 6 * b`
      have hT5 : lsfBatchSize tr.cs U ≤ 6 * b :=
        (lsfBatchSize_le hI hBU).trans (Nat.mul_le_mul_left 6 hb)
      -- Term 6: `info.newlyActive.sum tr.lazyMachInitCost`
      have hT6 : (stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').newlyActive.sum
          tr.lazyMachInitCost ≤
          W.spanConst * (4 * Γ * (115 * M + 4) ^ 2 + (L + 6) * (115 * M + 4)) * M :=
        stepBundleTreeMach_lazyMach_sum_le lsfInit W.C_lsst (fun _ => W.sparsify) W.params
          W.hp_s W.hp_t cfg.P.M₀
          (concreteBucketCapacity true W.C_lsst cfg.Ψ cfg.P.M₀ cfg.N₀
            ((by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two W).trans (le_max_right _ _))))
          W.spanConst k M N H.len hk1 hMsq H.D H.ord H.restarts
          H.hInitMBound H.hG0 hV₀ hℓ₀ H.hD H.hOrd H.len r le_rfl hInit_r U st.ord ord'
      -- Combine all 6 terms inside `branchStepCharge`.
      rw [htr_eq]
      unfold branchStepCharge
      dsimp only
      rw [hParams.1, hParams.2.1]
      have hS_def : dryStepCapS J j =
          3 * (k + 1) * M + (5 + 24 * B_j) * M +
            1080 * W.spanConst * Γ ^ 2 * (k + 1) ^ 2 * (115 * M + 4) * M +
            W.spanConst * (4 * Γ * (115 * M + 4) ^ 2 + (L + 6) * (115 * M + 4)) * M := rfl
      have hInner : U.length +
            ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').state.activeComps.sum fun C =>
              (tr.activeBuckets C).sum fun bkt =>
                (tr.dyn (C, bkt)).G.batchEnc
                  ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').U_B (C, bkt))) +
            tr.S_cur.batchEnc (stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').U_S +
            ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').state.activeComps.sum fun C =>
              (tr.activeBuckets C).sum fun bkt =>
                spanBatchChargeWith tr.spanConst tr.spanParams L
                  ((tr.initBunG (C, bkt)).n + tr.splitBound) (tr.initBunG (C, bkt))
                  (tr.dyn (C, bkt)).G
                  ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').U_B (C, bkt))) +
            lsfBatchSize tr.cs U +
            (stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').newlyActive.sum
              tr.lazyMachInitCost ≤
          (10 + 112 * B_j) * (dryStepCapS J j + b) := by
        have hsum_step : U.length +
            ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').state.activeComps.sum fun C =>
              (tr.activeBuckets C).sum fun bkt =>
                (tr.dyn (C, bkt)).G.batchEnc
                  ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').U_B (C, bkt))) +
            tr.S_cur.batchEnc (stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').U_S +
            ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').state.activeComps.sum fun C =>
              (tr.activeBuckets C).sum fun bkt =>
                spanBatchChargeWith tr.spanConst tr.spanParams L
                  ((tr.initBunG (C, bkt)).n + tr.splitBound) (tr.initBunG (C, bkt))
                  (tr.dyn (C, bkt)).G
                  ((stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').U_B (C, bkt))) +
            lsfBatchSize tr.cs U +
            (stepBundleTree (fun _ => W.sparsify) tr U st.ord ord').newlyActive.sum
              tr.lazyMachInitCost ≤
            dryStepCapS J j + (8 + 112 * B_j) * b := by
          rw [hS_def]
          have h112 : (1 + 112 * B_j) * b + b + 6 * b = (8 + 112 * B_j) * b := by ring
          omega
        refine hsum_step.trans ?_
        have hS_le : dryStepCapS J j ≤ (10 + 112 * B_j) * dryStepCapS J j :=
          Nat.le_mul_of_pos_left _ (by omega)
        have hb_le : (8 + 112 * B_j) * b ≤ (10 + 112 * B_j) * b :=
          Nat.mul_le_mul_right b (by omega)
        rw [Nat.mul_add]
        omega
      calc _ ≤ (10 + 112 * B_j) * (dryStepCapS J j + b) * B_j :=
            Nat.mul_le_mul_right B_j hInner
        _ = B_j * (10 + 112 * B_j) * (dryStepCapS J j + b) := by ring
    calc (Finset.range k).sum (fun r =>
            branchStepCharge (fun _ => W.sparsify) (st.trees r) U st.ord ord')
        ≤ (Finset.range k).sum (fun _ => B_j * (10 + 112 * B_j) * (dryStepCapS J j + b)) :=
          Finset.sum_le_sum hbranch
      _ = k * (B_j * (10 + 112 * B_j) * (dryStepCapS J j + b)) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ = dryInnerCoreStepCap J j b := by
          unfold dryInnerCoreStepCap dryStepCapR; ring
  · have hNM_full := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit W.C_lsst L
      (fun _ => W.sparsify) W.params W.spanConst k M N H.D H.ord H.restarts H.len).2.2
    have hne_b : ((sparseCoreBundleRestartToolWith lsfInit W.C_lsst L
        (fun _ => W.sparsify)).runOrdAfterRestarts k M N H.D H.ord H.restarts H.len).isNonempty = false :=
      (runOrdAfterRestarts_isNonempty lsfInit W.C_lsst L (fun _ => W.sparsify)
        k M N H.D H.ord H.restarts H.len).2.1.trans (decide_eq_false hV₀)
    have hne : st.isNonempty = false := by
      rw [hst_run, hNM_full.isNonempty]; exact hne_b
    have hup := asm_updateOrd_of_empty lsfInit W.C_lsst L (fun _ => W.sparsify) W.params
      W.spanConst st hne U ℓ g ord'
    change (sparseCoreBundleRestartToolMachWith lsfInit W.C_lsst L (fun _ => W.sparsify)
        W.params W.spanConst).cost
        ((sparseCoreBundleRestartToolMachWith lsfInit W.C_lsst L (fun _ => W.sparsify)
          W.params W.spanConst).updateOrd st U ℓ g ord').1 -
        (sparseCoreBundleRestartToolMachWith lsfInit W.C_lsst L (fun _ => W.sparsify)
          W.params W.spanConst).cost st ≤ _
    rw [hup, Nat.sub_self]
    exact Nat.zero_le _

/-- Full `BranchBToolStepKFBL` at the dry tool and `dryInnerCoreStepCap J` for every circulation
`J` (`hJn`, `hJm`, `hCapPos`) and every chain state `ch` meeting `ShiftLoopChainInv`. -/
theorem dryTool_branchBToolStepKFBL (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hInv : ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch) :
    BranchBToolStepKFBL (concreteCirculationCfgWithLast dryWitnessUsed J)
      (dryInnerCoreStepCap J) ch := by
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let kCap := cappedQualityExponent threshold (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let lsfInit := dryWitnessUsed.lsfInit (ipmQualityLimbs I.m V kCap) (ipmQualityPrecision I.m V kCap)
  let depth := Expander.chosenL (cfg.P.M₀ ^ 2)
  have hT : cfg.T = sparseCoreProgTool lsfInit dryWitnessUsed.C_lsst depth sparsifyImplUsed := rfl
  intro j hj U ℓ g ord' hOK
  have hbran : ch.bran j < (ch.scState j).k :=
    progTool_shiftLoop_bran_lt_k hT hInv hj
  refine ⟨?_, ?_, fun b hb =>
    dryTool_updateOrd_cost_sub_le J hJn hJm hCapPos hInv hj U ℓ g ord' hOK hb⟩
  · exact progTool_updateOrd_batchEnc_le_cost_sub (lsfInit := lsfInit)
      (C_lsst := dryWitnessUsed.C_lsst) (depth := depth) (impl := sparsifyImplUsed)
      (ch.scState j) U ℓ g ord' hbran
  · exact progTool_updateOrd_fwd_length_le_cost_sub (lsfInit := lsfInit)
      (C_lsst := dryWitnessUsed.C_lsst) (depth := depth) (impl := sparsifyImplUsed)
      (ch.scState j) U ℓ g ord' hbran

end MinCostFlow.Final.DryRun
