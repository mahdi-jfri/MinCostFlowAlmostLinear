module

public import MinCostFlow.MinRatio.OrdSolverCapDeposit
public import MinCostFlow.MinRatio.WireSpecBase
import MinCostFlow.MinRatio.ShiftInitQuota
import Mathlib.Tactic

/-!
# Dual credits for tool cost and tree updates, and `wire_credit_step` amortization bridges

Packages `runtimeCap` / `treeUpdateCap` together with `chainCapDeposit` and `capFwdPotential`
(`OrdSolverCapDeposit.lean`) into `runtimeCredit` and `treeCredit`, and proves the three
step-amortization lemmas (`wire_dual_credit_init_step`, `wire_dual_credit_shift_step`,
`wire_dual_credit_update_step`) using `wire_credit_step` (`WireSpecBase.lean`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain Chain.Ordered SparseCore SparseCore.Program Bundle

/-! ## 4. The two credits and `wire_credit_step` amortization lemmas -/

/-- The amortized credit for `ChainState.totalRuntime`: remaining cap credit plus the deposit and
forward potential feeding it from updates. -/
@[expose] noncomputable def runtimeCredit (cfg : Alg2Config) (model : Alg2State cfg) : ℕ :=
  (runtimeCap cfg model - model.chain.totalRuntime) +
    runtimeFactorNat cfg *
      (chainCapDeposit cfg model.chain + capFwdPotential cfg (fwdGamma cfg) model.chain)

/-- The amortized credit for `ChainState.totalTreeUpdates`: remaining cap credit plus the deposit
and forward potential feeding it from updates. -/
@[expose] noncomputable def treeCredit (cfg : Alg2Config) (model : Alg2State cfg) : ℕ :=
  (treeUpdateCap cfg model - model.chain.totalTreeUpdates) +
    treeUpdateFactorNat cfg *
      (chainCapDeposit cfg model.chain + capFwdPotential cfg (fwdGamma cfg) model.chain)

/-- At `Init`, both deposit and forward potential vanish, `largeBatchEnc = 0`, and
`runtimeCredit` + `totalRuntime` (resp. `treeCredit` + `totalTreeUpdates`) equals the initial cap
whenever the initial totals are below their caps. -/
theorem credits_init_le (cfg : Alg2Config) (G₀ : MGraph) (g₀ ℓ₀ : ℕ → ℝ) :
    let s0 := Ordered.algorithm2_init cfg G₀ g₀ ℓ₀
    chainCapDeposit cfg s0.chain = 0 ∧
    capFwdPotential cfg (fwdGamma cfg) s0.chain = 0 ∧
    runtimeCredit cfg s0 = runtimeCap cfg s0 - s0.chain.totalRuntime ∧
    treeCredit cfg s0 = treeUpdateCap cfg s0 - s0.chain.totalTreeUpdates ∧
    runtimeCap cfg s0 = chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) ∧
    treeUpdateCap cfg s0 = chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0) := by
  intro s0
  have hcnt := algorithm1_initialize_counts cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ G₀ ℓ₀ g₀
  have hupd : ∀ j, s0.chain.updCount j = 0 := hcnt.2.2.2.1
  have hfwd : ∀ j, s0.chain.curFwd j = 0 := hcnt.2.2.2.2
  have hrc : s0.chain.rebuildCount = fun _ => 0 := hcnt.2.1
  have hdep : chainCapDeposit cfg s0.chain = 0 := by
    unfold chainCapDeposit
    exact Finset.sum_eq_zero fun j _ => by rw [hupd j, mul_zero]
  have hfpot : capFwdPotential cfg (fwdGamma cfg) s0.chain = 0 := by
    unfold capFwdPotential
    exact Finset.sum_eq_zero fun j _ => by rw [hupd j, hfwd j]; simp
  have hlbe : ⌈s0.largeBatchEnc⌉₊ = 0 := by
    change ⌈(0 : ℝ)⌉₊ = 0; simp
  refine ⟨hdep, hfpot, by unfold runtimeCredit; rw [hdep, hfpot]; simp,
    by unfold treeCredit; rw [hdep, hfpot]; simp,
    by unfold runtimeCap; rw [hrc, hlbe, Nat.add_zero],
    by unfold treeUpdateCap; rw [hrc]⟩

/-- **Init amortization under the dual credits.** Turns an `Init` cost of the form
`initFixed + toolMul * s0.chain.totalRuntime + treeMul * s0.chain.totalTreeUpdates` (matching
`OrdInitConcreteSpecW`) into `initFixed + toolMul * runtimeCap s0 + treeMul * treeUpdateCap s0`
when adding `toolMul * runtimeCredit s0 + treeMul * treeCredit s0` to the potential. -/
theorem wire_dual_credit_init_step (cfg : Alg2Config) (G₀ : MGraph) (g₀ ℓ₀ : ℕ → ℝ)
    {cost phi initFixed toolMul treeMul : ℕ}
    (hcost : cost + phi ≤ initFixed +
      toolMul * (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀).chain.totalRuntime +
      treeMul * (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀).chain.totalTreeUpdates)
    (hRtCap : (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀).chain.totalRuntime ≤
      runtimeCap cfg (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀))
    (hTuCap : (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀).chain.totalTreeUpdates ≤
      treeUpdateCap cfg (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀)) :
    let s0 := Ordered.algorithm2_init cfg G₀ g₀ ℓ₀
    cost + (phi + toolMul * runtimeCredit cfg s0 + treeMul * treeCredit cfg s0) ≤
      initFixed +
        toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) +
        treeMul * chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0) := by
  intro s0
  obtain ⟨_, _, hrcC, htcC, hrc0, htc0⟩ := credits_init_le cfg G₀ g₀ ℓ₀
  rw [hrcC, htcC, ← hrc0, ← htc0]
  have h1 : toolMul * s0.chain.totalRuntime + toolMul * (runtimeCap cfg s0 - s0.chain.totalRuntime) =
      toolMul * runtimeCap cfg s0 := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hRtCap]
  have h2 : treeMul * s0.chain.totalTreeUpdates +
      treeMul * (treeUpdateCap cfg s0 - s0.chain.totalTreeUpdates) =
      treeMul * treeUpdateCap cfg s0 := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hTuCap]
  change cost + phi ≤ initFixed + toolMul * s0.chain.totalRuntime + treeMul * s0.chain.totalTreeUpdates at hcost
  change cost + (phi + toolMul * (runtimeCap cfg s0 - s0.chain.totalRuntime) +
      treeMul * (treeUpdateCap cfg s0 - s0.chain.totalTreeUpdates)) ≤
    initFixed + toolMul * runtimeCap cfg s0 + treeMul * treeUpdateCap cfg s0
  omega

/-- **Shift-step amortization under the dual credits** (via `wire_credit_step`). A shift step
costing `fixed + toolMul * Δ totalRuntime + treeMul * Δ totalTreeUpdates` costs at most `fixed`
after adding `toolMul * runtimeCredit + treeMul * treeCredit` to the potential. -/
theorem wire_dual_credit_shift_step (cfg : Alg2Config) (hM : ToolCostMono cfg.T)
    (model : Alg2State cfg) (i : Fin (cfg.P.d + 1))
    {cost phi phi' fixed toolMul treeMul : ℕ}
    (hcost : cost + phi' ≤ fixed +
      toolMul * ((alg2LoopShiftStep cfg model i).chain.totalRuntime - model.chain.totalRuntime) +
      treeMul * ((alg2LoopShiftStep cfg model i).chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
      phi)
    (hRtCap : (alg2LoopShiftStep cfg model i).chain.totalRuntime ≤
      runtimeCap cfg (alg2LoopShiftStep cfg model i))
    (hTuCap : (alg2LoopShiftStep cfg model i).chain.totalTreeUpdates ≤
      treeUpdateCap cfg (alg2LoopShiftStep cfg model i)) :
    let model' := alg2LoopShiftStep cfg model i
    cost + (phi' + toolMul * runtimeCredit cfg model' + treeMul * treeCredit cfg model') ≤
      fixed + (phi + toolMul * runtimeCredit cfg model + treeMul * treeCredit cfg model) := by
  intro model'
  have hRtM : model.chain.totalRuntime ≤ model'.chain.totalRuntime :=
    algorithm1_shift_totalRuntime_mono hM cfg.L cfg.P model.chain i.val
  have hTuM : model.chain.totalTreeUpdates ≤ model'.chain.totalTreeUpdates :=
    algorithm1_shift_totalTreeUpdates_mono cfg.T cfg.L cfg.P model.chain i.val
  obtain ⟨hRcapEq, hdepLe, hfwdLe⟩ :=
    algorithm1_shift_cap_le cfg (runtimeFactorNat cfg) (fwdGamma cfg) model.chain i.val
  obtain ⟨hTcapEq, _, _⟩ :=
    algorithm1_shift_cap_le cfg (treeUpdateFactorNat cfg) (fwdGamma cfg) model.chain i.val
  have hRcap : runtimeCap cfg model' = runtimeCap cfg model := by
    change chainRebuildCap cfg (runtimeFactorNat cfg)
        (Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1.rebuildCount +
      ⌈model.largeBatchEnc⌉₊ = _
    rw [hRcapEq]; rfl
  have hTcap : treeUpdateCap cfg model' = treeUpdateCap cfg model := hTcapEq
  change cost + phi' ≤ fixed +
    toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
    treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) + phi at hcost
  change model'.chain.totalRuntime ≤ runtimeCap cfg model' at hRtCap
  change model'.chain.totalTreeUpdates ≤ treeUpdateCap cfg model' at hTuCap
  have hstep1 := wire_credit_step (cost := cost) (phi := phi + treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates))
    (phi' := phi') (fixed := fixed) (mul := toolMul)
    (T := model.chain.totalRuntime) (T' := model'.chain.totalRuntime)
    (cap := runtimeCap cfg model) (by omega) hRtM (hRcap ▸ hRtCap)
  have hstep2 := wire_credit_step (cost := cost)
    (phi := phi + toolMul * (runtimeCap cfg model - model.chain.totalRuntime))
    (phi' := phi' + toolMul * (runtimeCap cfg model - model'.chain.totalRuntime))
    (fixed := fixed) (mul := treeMul)
    (T := model.chain.totalTreeUpdates) (T' := model'.chain.totalTreeUpdates)
    (cap := treeUpdateCap cfg model) (by omega) hTuM (hTcap ▸ hTuCap)
  unfold runtimeCredit treeCredit
  rw [hRcap, hTcap]
  have hdm : runtimeFactorNat cfg * (chainCapDeposit cfg model'.chain + capFwdPotential cfg (fwdGamma cfg) model'.chain) ≤
      runtimeFactorNat cfg * (chainCapDeposit cfg model.chain + capFwdPotential cfg (fwdGamma cfg) model.chain) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add hdepLe hfwdLe)
  have htm : treeUpdateFactorNat cfg * (chainCapDeposit cfg model'.chain + capFwdPotential cfg (fwdGamma cfg) model'.chain) ≤
      treeUpdateFactorNat cfg * (chainCapDeposit cfg model.chain + capFwdPotential cfg (fwdGamma cfg) model.chain) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add hdepLe hfwdLe)
  have hdm' := Nat.mul_le_mul_left toolMul hdm
  have htm' := Nat.mul_le_mul_left treeMul htm
  rw [Nat.mul_add toolMul, Nat.mul_add toolMul, Nat.mul_add treeMul, Nat.mul_add treeMul]
  omega

/-- Per-update amortized charge of `runtimeCredit` and `treeCredit` for a batch of length `uLen`. -/
@[expose] noncomputable def updateCreditCharge (cfg : Alg2Config) (toolMul treeMul : ℕ)
    (U : List Update) : ℕ :=
  toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 * U.length +
    ⌈largeBatchEncCap cfg.P U⌉₊) +
  treeMul * (treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 * U.length)

private theorem largeBatchEncCap_eq_of_length_eq (P : ChainParams) {U U' : List Update}
    (hlen : U'.length = U.length) :
    largeBatchEncCap P U' = largeBatchEncCap P U := by
  unfold largeBatchEncCap; rw [hlen]

/-- **Update amortization under the dual credits.** Turns an `Update` step whose combined
`ChainRefresh` + `CycleLoop` cost has `toolMul * Δ totalRuntime + treeMul * Δ totalTreeUpdates`
into an amortized cost adding `updateCreditCharge cfg toolMul treeMul U`, under
`toolMul * runtimeCredit + treeMul * treeCredit`. -/
theorem wire_dual_credit_update_step (cfg : Alg2Config) (κ : ℝ)
    (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ) (actual : ℝ)
    {cost phi phi' fixed toolMul treeMul : ℕ}
    (hfr : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hValid : model.extG.BatchIsValid U)
    (hBefore : FwdBoundNat cfg.P (fwdGamma cfg) model.chain)
    (hPre : FwdBoundNat cfg.P (fwdGamma cfg) (alg2PreLoopState cfg model U gVec lVec).chain)
    (hRtBefore : model.chain.totalRuntime ≤ runtimeCap cfg model)
    (hTuBefore : model.chain.totalTreeUpdates ≤ treeUpdateCap cfg model)
    (hRtAfter : ((Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1.chain.totalRuntime ≤
      runtimeCap cfg ((Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1)
    (hTuAfter : ((Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1.chain.totalTreeUpdates ≤
      treeUpdateCap cfg ((Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1)
    (hcost : cost + phi' +
        toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
      fixed + phi +
        toolMul * ((Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1.chain.totalRuntime +
        treeMul * ((Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1.chain.totalTreeUpdates) :
    let model' := ((Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual).1
    cost + (phi' + toolMul * runtimeCredit cfg model' + treeMul * treeCredit cfg model') ≤
      fixed + updateCreditCharge cfg toolMul treeMul U +
        (phi + toolMul * runtimeCredit cfg model + treeMul * treeCredit cfg model) := by
  intro model'
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let U_int := tr.2.2.2.2
  let ch1 := (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain U_int
    (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e'))).1
  have hUlen : U_int.length = U.length :=
    (translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt model.intToExt
      model.nextFresh hfr hValid).2.2.2.2.1
  have hch1Eq : (alg2PreLoopState cfg model U gVec lVec).chain = ch1 := rfl
  have hPre' : FwdBoundNat cfg.P (fwdGamma cfg) ch1 := hch1Eq ▸ hPre
  -- Relate `model'` to `algorithm2_loopWith` starting from `ch1`
  have hloopRel :
      chainRebuildCap cfg (runtimeFactorNat cfg) model'.chain.rebuildCount =
        chainRebuildCap cfg (runtimeFactorNat cfg) ch1.rebuildCount ∧
      chainRebuildCap cfg (treeUpdateFactorNat cfg) model'.chain.rebuildCount =
        chainRebuildCap cfg (treeUpdateFactorNat cfg) ch1.rebuildCount ∧
      chainCapDeposit cfg model'.chain ≤ chainCapDeposit cfg ch1 ∧
      capFwdPotential cfg (fwdGamma cfg) model'.chain ≤ capFwdPotential cfg (fwdGamma cfg) ch1 ∧
      model'.largeBatchEnc = model.largeBatchEnc + largeBatchEncCap cfg.P U_int := by
    have hchEnd : model'.chain = (Ordered.algorithm2_loopWith cfg κ tr.1
        (level0E2I (level0Rebuilt cfg.P.d model.chain.rebuildCount ch1.rebuildCount)
          ((model.chain.G 0).applyBatch U_int) tr.2.1)
        gVec lVec ch1
        (match firstRebuiltLevel cfg.P.d model.chain.rebuildCount ch1.rebuildCount with
          | none => (model.branD, model.passes)
          | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else model.passes j)).1
        (match firstRebuiltLevel cfg.P.d model.chain.rebuildCount ch1.rebuildCount with
          | none => (model.branD, model.passes)
          | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else model.passes j)).2
        (model.lctUpdateOps + U.length)).1 ∧
        model'.largeBatchEnc = model.largeBatchEnc + largeBatchEncCap cfg.P U_int := by
      change (Ordered.algorithm2_updateWith cfg κ model U gVec lVec actual).1.chain = _ ∧
        (Ordered.algorithm2_updateWith cfg κ model U gVec lVec actual).1.largeBatchEnc = _
      unfold Ordered.algorithm2_updateWith
      dsimp only [tr, U_int, ch1]
      split <;> exact ⟨rfl, rfl⟩
    obtain ⟨h1, h2, h3⟩ := algorithm2_loopWith_cap_le cfg (runtimeFactorNat cfg) (fwdGamma cfg) κ
      tr.1 _ gVec lVec ch1 _ _ (model.lctUpdateOps + U.length)
    obtain ⟨h1', _, _⟩ := algorithm2_loopWith_cap_le cfg (treeUpdateFactorNat cfg) (fwdGamma cfg) κ
      tr.1 _ gVec lVec ch1 _ _ (model.lctUpdateOps + U.length)
    rw [hchEnd.1]
    exact ⟨h1, h1', h2, h3, hchEnd.2⟩
  obtain ⟨hRloop, hTloop, hDloop, hFloop, hLbe⟩ := hloopRel
  have hRam := algorithm1_update_cap_amortized cfg (runtimeFactorNat cfg) (fwdGamma cfg)
    model.chain U_int (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e')) hBefore hPre'
  have hTam := algorithm1_update_cap_amortized cfg (treeUpdateFactorNat cfg) (fwdGamma cfg)
    model.chain U_int (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e')) hBefore hPre'
  rw [hUlen] at hRam hTam
  have hLbeCeil : ⌈model'.largeBatchEnc⌉₊ ≤ ⌈model.largeBatchEnc⌉₊ + ⌈largeBatchEncCap cfg.P U⌉₊ := by
    rw [hLbe, largeBatchEncCap_eq_of_length_eq cfg.P hUlen]
    exact Nat.ceil_add_le _ _
  have hRtTot : runtimeCap cfg model' +
      runtimeFactorNat cfg * (chainCapDeposit cfg model'.chain + capFwdPotential cfg (fwdGamma cfg) model'.chain) ≤
      runtimeCap cfg model +
      runtimeFactorNat cfg * (chainCapDeposit cfg model.chain + capFwdPotential cfg (fwdGamma cfg) model.chain) +
      (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 * U.length + ⌈largeBatchEncCap cfg.P U⌉₊) := by
    unfold runtimeCap
    rw [hRloop]
    have hmul : runtimeFactorNat cfg * (chainCapDeposit cfg model'.chain + capFwdPotential cfg (fwdGamma cfg) model'.chain) ≤
        runtimeFactorNat cfg * (chainCapDeposit cfg ch1 + capFwdPotential cfg (fwdGamma cfg) ch1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add hDloop hFloop)
    change chainRebuildCap cfg (runtimeFactorNat cfg) ch1.rebuildCount +
      runtimeFactorNat cfg * (chainCapDeposit cfg ch1 + capFwdPotential cfg (fwdGamma cfg) ch1) ≤ _ at hRam
    omega
  have hTuTot : treeUpdateCap cfg model' +
      treeUpdateFactorNat cfg * (chainCapDeposit cfg model'.chain + capFwdPotential cfg (fwdGamma cfg) model'.chain) ≤
      treeUpdateCap cfg model +
      treeUpdateFactorNat cfg * (chainCapDeposit cfg model.chain + capFwdPotential cfg (fwdGamma cfg) model.chain) +
      treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 * U.length := by
    unfold treeUpdateCap
    rw [hTloop]
    have hmul : treeUpdateFactorNat cfg * (chainCapDeposit cfg model'.chain + capFwdPotential cfg (fwdGamma cfg) model'.chain) ≤
        treeUpdateFactorNat cfg * (chainCapDeposit cfg ch1 + capFwdPotential cfg (fwdGamma cfg) ch1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add hDloop hFloop)
    change chainRebuildCap cfg (treeUpdateFactorNat cfg) ch1.rebuildCount +
      treeUpdateFactorNat cfg * (chainCapDeposit cfg ch1 + capFwdPotential cfg (fwdGamma cfg) ch1) ≤ _ at hTam
    omega
  -- Combine `hRtTot`, `hTuTot`, and `hcost` via `runtimeCredit` / `treeCredit`
  have hRtSplit1 : runtimeCredit cfg model + model.chain.totalRuntime =
      runtimeCap cfg model +
        runtimeFactorNat cfg * (chainCapDeposit cfg model.chain + capFwdPotential cfg (fwdGamma cfg) model.chain) := by
    unfold runtimeCredit; omega
  have hRtSplit2 : runtimeCredit cfg model' + model'.chain.totalRuntime =
      runtimeCap cfg model' +
        runtimeFactorNat cfg * (chainCapDeposit cfg model'.chain + capFwdPotential cfg (fwdGamma cfg) model'.chain) := by
    change model'.chain.totalRuntime ≤ runtimeCap cfg model' at hRtAfter
    unfold runtimeCredit; omega
  have hTuSplit1 : treeCredit cfg model + model.chain.totalTreeUpdates =
      treeUpdateCap cfg model +
        treeUpdateFactorNat cfg * (chainCapDeposit cfg model.chain + capFwdPotential cfg (fwdGamma cfg) model.chain) := by
    unfold treeCredit; omega
  have hTuSplit2 : treeCredit cfg model' + model'.chain.totalTreeUpdates =
      treeUpdateCap cfg model' +
        treeUpdateFactorNat cfg * (chainCapDeposit cfg model'.chain + capFwdPotential cfg (fwdGamma cfg) model'.chain) := by
    change model'.chain.totalTreeUpdates ≤ treeUpdateCap cfg model' at hTuAfter
    unfold treeCredit; omega
  have hRtMul := Nat.mul_le_mul_left toolMul hRtTot
  have hTuMul := Nat.mul_le_mul_left treeMul hTuTot
  rw [← hRtSplit1, ← hRtSplit2, Nat.mul_add toolMul, Nat.mul_add toolMul, Nat.mul_add toolMul] at hRtMul
  rw [← hTuSplit1, ← hTuSplit2, Nat.mul_add treeMul, Nat.mul_add treeMul, Nat.mul_add treeMul] at hTuMul
  change cost + phi' + toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
    fixed + phi + toolMul * model'.chain.totalRuntime + treeMul * model'.chain.totalTreeUpdates at hcost
  unfold updateCreditCharge
  omega

end MinCostFlow.MinRatio
