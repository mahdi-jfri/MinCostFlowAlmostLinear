module

public import MinCostFlow.LSF.Program.LSFModule
public import MinCostFlow.LSF.Program.Lemma55Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Module Assembly and Weight-Update Loop for Lemma 5.5 (`Lemma55ProgramBase`)

Defines the relocatable layout (`lemma55ModuleProcs`, `lemma55Module`), proves determinism
(`lemma55Module_isDeterministic`), `HasAt` extraction (`hasAt_lsf_utils_and_c1`,
`lemma55HasAt_split`), and verifies the per-round edge-weight update loop (`mwuWeightsLoop_runs`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  MinCostFlow.Num

@[expose] public section

/-! ## Submodule lengths and relocatable layout -/

lemma fixedDivideModule_length (b h : ℕ) : (fixedDivideModule b h).length = 32 := by
  simp [fixedDivideModule, signExtendModule, isNegativeModule, extendCopyModule,
    shiftLeftModule, integerDivideModule_length, copyModule]

lemma fixedMultiplyModule_length (b h : ℕ) : (fixedMultiplyModule b h).length = 11 := by
  simp [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule]

lemma positiveExponentialModule_length (b h : ℕ) : (positiveExponentialModule b h).length = 58 := by
  simp [positiveExponentialModule, shiftRightModule, expHornerModule, roundedSquaringModule,
    copyModule, fixedMultiplyModule_length, loadSmallModule, integerDivideModule_length,
    addCarryModule]

def lemma55IdxInit : ℕ := 0
def lemma55BaseLsf (b : ℕ) : ℕ := b + 5
def lemma55BaseDiv (Q_AN : Program) (b : ℕ) : ℕ := lemma55BaseLsf b + (257 + Q_AN.procs.length)
def lemma55BaseExp (Q_AN : Program) (b : ℕ) : ℕ := lemma55BaseDiv Q_AN b + 32
def lemma55BaseMul (Q_AN : Program) (b : ℕ) : ℕ := lemma55BaseExp Q_AN b + 58
def lemma55ModuleEnd (Q_AN : Program) (b : ℕ) : ℕ := lemma55BaseMul Q_AN b + 11

/-! ## Procedures: `mwuWeightsLoopProc` and `lemma55InitProc` -/

/-- Update all `m₀` active edge weights in `wtArr` using the rational stretches of `lsfHandle`.
Args: `[g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap]`. Returns `0`. -/
def mwuWeightsLoopProc (bEdgeStep : ℕ) : Stmt :=
  .assign 9 (.load (.bin .add (.reg 0) (.const dgVCapOff))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const dgECapOff))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const dgMOff))) ;;
  .assign 12 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 7) (.reg 9))) (.reg 10)) ;;
  .assign 13 (.load (.bin .add (.reg 1) (.const lsfOffWstrNumPtr))) ;;
  .assign 14 (.load (.bin .add (.reg 1) (.const lsfOffWstrDenPtr))) ;;
  forRange 15 (.const 0) (.reg 11)
    (.assign 16 (.load (.bin .add (.reg 12) (.reg 15))) ;;
     .assign 17 (.bin .add (.reg 13) (.bin .mul (.reg 16) (.reg 6))) ;;
     .assign 18 (.bin .add (.reg 14) (.bin .mul (.reg 16) (.reg 6))) ;;
     .assign 19 (.bin .add (.reg 2) (.bin .mul (.reg 16) (.reg 5))) ;;
     .call 20 bEdgeStep [.reg 17, .reg 18, .reg 19, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8]) ;;
  .ret (.const 0)

lemma mwuWeightsLoopProc_noRand (bEdgeStep : ℕ) : (mwuWeightsLoopProc bEdgeStep).NoRand := by
  simp [mwuWeightsLoopProc, forRange, forUp, Stmt.NoRand]

/-- Main Lemma 5.5 initialization procedure: allocates `[wtArr, onePtr, rhoPtr]` at `heap`,
computes `ρ · 2^P_fp`, initializes `v₀ ≡ 1`, and runs `k_nat` rounds of `lsfInit` + MWU weight
updates, storing handle `j` at `handlesOut + j`.
Args: `[g0Ptr, lenArr, L_in, P_fp, k_nat, L_w, vCap, eCap, handlesOut, heap]`.
Returns final heap pointer `curHeap`. -/
def lemma55InitProc (bBuildRho bLsfInit bWeightsLoop h : ℕ) : Stmt :=
  .assign 10 (.reg 9) ;;
  .assign 11 (.bin .add (.reg 10) (.bin .mul (.reg 7) (.reg 2))) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 5)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 5)) ;;
  .assign 14 (.bin .div (.reg 3) (.const h)) ;;
  .store (.bin .add (.reg 11) (.reg 14)) (.const 1) ;;
  .assign 15 (.load (.bin .add (.reg 0) (.const dgNOff))) ;;
  .call 16 bBuildRho [.reg 12, .reg 15, .reg 4, .reg 5, .reg 14, .reg 13] ;;
  .assign 16 (.load (.bin .add (.reg 0) (.const dgVCapOff))) ;;
  .assign 17 (.load (.bin .add (.reg 0) (.const dgECapOff))) ;;
  .assign 18 (.load (.bin .add (.reg 0) (.const dgMOff))) ;;
  .assign 19 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 7) (.reg 16))) (.reg 17)) ;;
  forRange 16 (.const 0) (.reg 18)
    (.assign 17 (.load (.bin .add (.reg 19) (.reg 16))) ;;
     .store (.bin .add (.bin .add (.reg 10) (.bin .mul (.reg 17) (.reg 2))) (.reg 14)) (.const 1)) ;;
  forRange 16 (.const 0) (.reg 4)
    (.call 17 bLsfInit [.reg 0, .reg 1, .reg 10, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 13] ;;
     .store (.bin .add (.reg 8) (.reg 16)) (.reg 13) ;;
     .call 18 bWeightsLoop [.reg 0, .reg 13, .reg 10, .reg 11, .reg 12, .reg 2, .reg 5, .reg 3, .reg 17] ;;
     .assign 13 (.reg 17)) ;;
  .ret (.reg 13)

lemma lemma55InitProc_noRand (bBuildRho bLsfInit bWeightsLoop h : ℕ) :
    (lemma55InitProc bBuildRho bLsfInit bWeightsLoop h).NoRand := by
  simp [lemma55InitProc, forRange, forUp, Stmt.NoRand]

/-- Complete relocatable procedure block for Lemma 5.5 starting at index `b`.
Entry `b + 0` is `lemma55InitProc`; `lemma55BaseLsf b + lsfIdxBatch` is `ApplyBatch`. -/
noncomputable def lemma55ModuleProcs (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (b h : ℕ) : List Stmt :=
  let bLsf := lemma55BaseLsf b
  let bDiv := lemma55BaseDiv Q_AN b
  let bExp := lemma55BaseExp Q_AN b
  let bMul := lemma55BaseMul Q_AN b
  let u := lsfBaseUtils bLsf
  let c1 := lsfBaseC1 Q_AN bLsf
  [ lemma55InitProc (b + 3) (bLsf + lsfIdxInit) (b + 1) h
  , mwuWeightsLoopProc (b + 2)
  , mwuEdgeStepProc bDiv bExp bMul (u + idxUtilMemCopy) (u + idxUtilMemFill)
  , buildRhoFpProc (u + idxUtilLog2) (b + 4) (c1 + 1) (c1 + 2) (u + idxUtilMemFill)
  , emitNatStmt (lemma55RhoConst K_AN) h ] ++
  lsfModuleProcs Q_AN c_AN K_AN bLsf h ++
  fixedDivideModule bDiv h ++
  positiveExponentialModule bExp h ++
  fixedMultiplyModule bMul h

/-- Standalone deterministic Word-RAM program for Lemma 5.5. -/
noncomputable def lemma55Module (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (h : ℕ) : Program :=
  ⟨lemma55ModuleProcs Q_AN c_AN K_AN 0 h⟩

lemma lemma55ModuleProcs_length (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (b h : ℕ) :
    (lemma55ModuleProcs Q_AN c_AN K_AN b h).length = 363 + Q_AN.procs.length := by
  simp only [lemma55ModuleProcs, List.length_append, lsfModuleProcs_length,
    fixedDivideModule_length, positiveExponentialModule_length, fixedMultiplyModule_length,
    List.length_cons, List.length_nil]
  omega

lemma lemma55ModuleProcs_noRand (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (b h : ℕ) :
    ∀ s ∈ lemma55ModuleProcs Q_AN c_AN K_AN b h, s.NoRand := by
  intro s hs
  simp only [lemma55ModuleProcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with ((((rfl | rfl | rfl | rfl | rfl) | h1) | h2) | h3) | h4
  · exact lemma55InitProc_noRand _ _ _ _
  · exact mwuWeightsLoopProc_noRand _
  · exact mwuEdgeStepProc_noRand _ _ _ _ _
  · exact buildRhoFpProc_noRand _ _ _ _ _
  · exact emitNatStmt_noRand _ _
  · exact lsfModuleProcs_noRand Q_AN c_AN K_AN _ h s h1
  · exact fixedDivideModule_noRand _ h s h2
  · exact positiveExponentialModule_noRand _ h s h3
  · exact fixedMultiplyModule_noRand _ h s h4

/-- `lemma55Module` is completely deterministic (contains no `rand` statements). -/
theorem lemma55Module_isDeterministic (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (h : ℕ) :
    (lemma55Module Q_AN c_AN K_AN h).IsDeterministic :=
  lemma55ModuleProcs_noRand Q_AN c_AN K_AN 0 h

/-! ## `HasAt` extraction helpers -/

lemma hasAt_cast' {p : Program} {a : ℕ} (b : ℕ) {xs : List Stmt}
    (h : p.HasAt a xs) (heq : a = b) : p.HasAt b xs := heq ▸ h

lemma hasAt_lsf_utils_and_c1 {p Q_AN : Program} {c_AN bLsf h : ℕ} {K_AN : ℝ}
    (hp : p.HasAt bLsf (lsfModuleProcs Q_AN c_AN K_AN bLsf h)) :
    p.HasAt (bLsf + 2) (lsfSharedProcs bLsf (lsfKNat K_AN) h) ∧
    p.HasAt (lsfBaseC1 Q_AN bLsf) (lsfProcsC1 Q_AN bLsf h) := by
  have hp0 : p.HasAt bLsf
      ([lsfInitBody (lsfInitIdx Q_AN bLsf) (lsfBaseOne Q_AN bLsf + 0) (lsfBaseOne Q_AN bLsf + 1)
          (lsfBaseOne Q_AN bLsf + 2) h,
        lsfApplyBatchProc (lsfBaseBat Q_AN bLsf + 7) (lsfBaseBat Q_AN bLsf + 8)
          (lsfBaseBat Q_AN bLsf + 9)] ++
       (lsfSharedProcs bLsf (lsfKNat K_AN) h ++
        (lsstModule Q_AN (lsfBaseLsst bLsf) h ++
         (lsfProcsA1 Q_AN c_AN bLsf h ++
          (lsfProcsA2 Q_AN bLsf h ++
           (lsfProcsB1 Q_AN bLsf ++
            (lsfProcsB2 Q_AN bLsf h ++
             (lsfProcsC1 Q_AN bLsf h ++
              (lsfProcsC2 Q_AN bLsf ++
               (lsfProcsD Q_AN bLsf h ++
                (lsfProcsOne h ++ lsfProcsBat Q_AN bLsf))))))))))) := by
    simpa only [lsfModuleProcs, List.append_assoc] using hp
  have r1 := hasAt_cast' (bLsf + 2) (Num.hasAt_append_right hp0) (by simp)
  have hSh := Num.hasAt_append_left r1
  have r2 := hasAt_cast' (lsfBaseLsst bLsf) (Num.hasAt_append_right r1) (by
    rw [lsfSharedProcs_length]
    dsimp only [lsfBaseLsst, lsfSharedEnd, lsfBaseUtils, lsfBaseIntDiv, lsfBaseMul, lsfBaseSub,
      lsfBaseAdd, lsfBaseShiftL, lsfBaseLess, lsfBaseCopy, lsfBaseSort, lsfBaseDg])
  have r3 := hasAt_cast' (lsfBaseA1 Q_AN bLsf) (Num.hasAt_append_right r2) (by rw [lsstModule_length]; rfl)
  have r4 := hasAt_cast' (lsfBaseA2 Q_AN bLsf) (Num.hasAt_append_right r3) (by rw [lsfProcsA1_length]; rfl)
  have r5 := hasAt_cast' (lsfBaseB1 Q_AN bLsf) (Num.hasAt_append_right r4) (by rw [lsfProcsA2_length]; rfl)
  have r6 := hasAt_cast' (lsfBaseB2 Q_AN bLsf) (Num.hasAt_append_right r5) (by rw [lsfProcsB1_length]; rfl)
  have r7 := hasAt_cast' (lsfBaseC1 Q_AN bLsf) (Num.hasAt_append_right r6) (by rw [lsfProcsB2_length]; rfl)
  exact ⟨hSh, Num.hasAt_append_left r7⟩

lemma lemma55HasAt_split {p Q_AN : Program} {c_AN b h : ℕ} {K_AN : ℝ}
    (hp : p.HasAt b (lemma55ModuleProcs Q_AN c_AN K_AN b h)) :
    let bLsf := lemma55BaseLsf b
    let bDiv := lemma55BaseDiv Q_AN b
    let bExp := lemma55BaseExp Q_AN b
    let bMul := lemma55BaseMul Q_AN b
    let u := lsfBaseUtils bLsf
    let c1 := lsfBaseC1 Q_AN bLsf
    p.procs[b + 0]? = some (lemma55InitProc (b + 3) (bLsf + lsfIdxInit) (b + 1) h) ∧
    p.procs[b + 1]? = some (mwuWeightsLoopProc (b + 2)) ∧
    p.procs[b + 2]? = some (mwuEdgeStepProc bDiv bExp bMul (u + idxUtilMemCopy) (u + idxUtilMemFill)) ∧
    p.procs[b + 3]? = some (buildRhoFpProc (u + idxUtilLog2) (b + 4) (c1 + 1) (c1 + 2) (u + idxUtilMemFill)) ∧
    p.procs[b + 4]? = some (emitNatStmt (lemma55RhoConst K_AN) h) ∧
    p.HasAt bLsf (lsfModuleProcs Q_AN c_AN K_AN bLsf h) ∧
    p.HasAt bDiv (fixedDivideModule bDiv h) ∧
    p.HasAt bExp (positiveExponentialModule bExp h) ∧
    p.HasAt bMul (fixedMultiplyModule bMul h) := by
  dsimp only
  set bLsf := lemma55BaseLsf b
  set bDiv := lemma55BaseDiv Q_AN b
  set bExp := lemma55BaseExp Q_AN b
  set bMul := lemma55BaseMul Q_AN b
  set u := lsfBaseUtils bLsf
  set c1 := lsfBaseC1 Q_AN bLsf
  have hp0 : p.HasAt b
      ([ lemma55InitProc (b + 3) (bLsf + lsfIdxInit) (b + 1) h
       , mwuWeightsLoopProc (b + 2)
       , mwuEdgeStepProc bDiv bExp bMul (u + idxUtilMemCopy) (u + idxUtilMemFill)
       , buildRhoFpProc (u + idxUtilLog2) (b + 4) (c1 + 1) (c1 + 2) (u + idxUtilMemFill)
       , emitNatStmt (lemma55RhoConst K_AN) h ] ++
       (lsfModuleProcs Q_AN c_AN K_AN bLsf h ++
        (fixedDivideModule bDiv h ++
         (positiveExponentialModule bExp h ++ fixedMultiplyModule bMul h)))) := by
    simpa only [lemma55ModuleProcs, List.append_assoc] using hp
  have hHdr := Num.hasAt_append_left hp0
  have r1 := hasAt_cast' bLsf (Num.hasAt_append_right hp0) (by simp [bLsf, lemma55BaseLsf])
  have hLsf := Num.hasAt_append_left r1
  have r2 := hasAt_cast' bDiv (Num.hasAt_append_right r1) (by
    rw [lsfModuleProcs_length]; rfl)
  have hDiv := Num.hasAt_append_left r2
  have r3 := hasAt_cast' bExp (Num.hasAt_append_right r2) (by
    rw [fixedDivideModule_length]; rfl)
  have hExp := Num.hasAt_append_left r3
  have hMul := hasAt_cast' bMul (Num.hasAt_append_right r3) (by
    rw [positiveExponentialModule_length]; rfl)
  exact ⟨hHdr.get (i := 0) (by simp), hHdr.get (i := 1) (by simp), hHdr.get (i := 2) (by simp),
    hHdr.get (i := 3) (by simp), hHdr.get (i := 4) (by simp), hLsf, hDiv, hExp, hMul⟩

lemma runs_seq_of_runs' {w k T : ℕ} {p : Program} {ω : ℕ → Bool} {s1 s2 : Stmt}
    {st st1 : State} {c1 : ℕ} {Q : Outcome → State → Prop}
    (h1 : Runs w p ω s1 st .normal st1 c1)
    (h2 : ∃ o st' c2, Runs w p ω s2 st1 o st' c2 ∧ Q o st' ∧ (k + c1 + 1) + c2 ≤ T) :
    ∃ o st' c, Runs w p ω (s1 ;; s2) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h2 with ⟨o, st', c2, hr2, hq, hle⟩
  exact ⟨o, st', c1 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, h1, hr2, rfl⟩), hq, by omega⟩

lemma runs_seq_of_exists' {w k T : ℕ} {p : Program} {ω : ℕ → Bool} {s1 s2 : Stmt}
    {st : State} {Q : Outcome → State → Prop} {P : State → ℕ → Prop}
    (h1 : ∃ st1 c1, Runs w p ω s1 st .normal st1 c1 ∧ P st1 c1)
    (h2 : ∀ st1 c1, P st1 c1 → ∃ o st' c2, Runs w p ω s2 st1 o st' c2 ∧ Q o st' ∧ (k + c1 + 1) + c2 ≤ T) :
    ∃ o st' c, Runs w p ω (s1 ;; s2) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h1 with ⟨st1, c1, hr1, hp1⟩
  rcases h2 st1 c1 hp1 with ⟨o, st', c2, hr2, hq, hle⟩
  exact ⟨o, st', c1 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, hr1, hr2, rfl⟩), hq, by omega⟩

/-! ## Helper 1: `mwuWeightsLoop_runs` -/

lemma mwuWeightsInner_runs {w h q bEdgeStep bDiv bExp bMul bCopy bFill
    wtArr onePtr rhoPtr L_in L_w P_fp tmpHeap k_nat rho_nat eCap0 eListPtr wstrNumPtr wstrDenPtr : ℕ}
    {G₀ : MGraph} {S_cur : LSFState} {v_cur : ℕ → ℝ} {eList : List ℕ} {p : Program}
    {ω : ℕ → Bool} {mem0 : ℕ → ℕ}
    (hh : 1 ≤ h) (hw : 3 * h + 2 ≤ w) (hLin_le : L_in ≤ L_w) (hk : 1 ≤ k_nat)
    (hdiv : h ∣ P_fp) (hq_P : q + 11 ≤ P_fp) (hk_q : 8 * k_nat ≤ 2 ^ q)
    (hP_Lin : P_fp + 6 ≤ h * L_in)
    (hm_Lin : 32 * (G₀.E.card + 1) * 2 ^ P_fp < 2 ^ (h * L_in - 1))
    (h2P_ltw : 2 * P_fp + 9 < 2 ^ w)
    (hrho_pos : 1 ≤ rho_nat) (hrho_cap : rho_nat < 2 ^ (h * (L_w - L_in)))
    (hpStep : p.procs[bEdgeStep]? = some (mwuEdgeStepProc bDiv bExp bMul bCopy bFill))
    (hDiv : MeetsContract w p bDiv (fixedDivideContract w h))
    (hExp : MeetsContract w p bExp (positiveExponentialContract w h q))
    (hMul : MeetsContract w p bMul (fixedMultiplyContract w h))
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hFill : MeetsContract w p bFill (memFillContract w))
    (heL_len : eList.length = G₀.E.card) (heL_nd : eList.Nodup)
    (heL_mem : ∀ e, e ∈ eList ↔ e ∈ G₀.E) (heL_at : ListAt mem0 eListPtr eList)
    (he_lt : ∀ e ∈ G₀.E, e < eCap0)
    (heL_le : eListPtr + G₀.E.card ≤ tmpHeap)
    (heL_disj : eListPtr + G₀.E.card ≤ wtArr ∨ wtArr + eCap0 * L_in ≤ eListPtr)
    (hwt_le : wtArr + eCap0 * L_in ≤ tmpHeap)
    (hone_le : onePtr + L_w ≤ tmpHeap) (hone_disj : onePtr + L_w ≤ wtArr ∨ wtArr + eCap0 * L_in ≤ onePtr)
    (hrho_le : rhoPtr + L_w ≤ tmpHeap) (hrho_disj : rhoPtr + L_w ≤ wtArr ∨ wtArr + eCap0 * L_in ≤ rhoPtr)
    (hnum_le : wstrNumPtr + eCap0 * L_w ≤ tmpHeap)
    (hnum_disj : wstrNumPtr + eCap0 * L_w ≤ wtArr ∨ wtArr + eCap0 * L_in ≤ wstrNumPtr)
    (hden_le : wstrDenPtr + eCap0 * L_w ≤ tmpHeap)
    (hden_disj : wstrDenPtr + eCap0 * L_w ≤ wtArr ∨ wtArr + eCap0 * L_in ≤ wstrDenPtr)
    (hsp : tmpHeap + mwuEdgeStepSpace L_in L_w P_fp < 2 ^ w)
    (hv_one : Valid mem0 onePtr h L_w) (hone_eq : intVal mem0 onePtr h L_w = (2 : ℤ) ^ P_fp)
    (hv_rho : Valid mem0 rhoPtr h L_w) (hrho_eq : intVal mem0 rhoPtr h L_w = (rho_nat : ℤ) * (2 : ℤ) ^ P_fp)
    (hWstr : ∀ e ∈ G₀.E,
      Valid mem0 (wstrNumPtr + e * L_w) h L_w ∧ Valid mem0 (wstrDenPtr + e * L_w) h L_w ∧
      0 < intVal mem0 (wstrNumPtr + e * L_w) h L_w ∧ 0 < intVal mem0 (wstrDenPtr + e * L_w) h L_w ∧
      (intVal mem0 (wstrNumPtr + e * L_w) h L_w : ℝ) / (intVal mem0 (wstrDenPtr + e * L_w) h L_w : ℝ) =
        S_cur.wstr e ∧
      1 ≤ S_cur.wstr e ∧ S_cur.wstr e ≤ (rho_nat : ℝ) / 10)
    (hwt0 : ∀ e ∈ G₀.E,
      Valid mem0 (wtArr + e * L_in) h L_in ∧
      fixVal mem0 (wtArr + e * L_in) h L_in P_fp = v_cur e ∧
      (1 / 2 : ℝ) ≤ v_cur e ∧ v_cur e ≤ 8 * (G₀.E.card : ℝ)) :
    ∀ idx ≤ eList.length, ∀ st : State,
      st.regs 2 = wtArr → st.regs 3 = onePtr → st.regs 4 = rhoPtr →
      st.regs 5 = L_in → st.regs 6 = L_w → st.regs 7 = P_fp → st.regs 8 = tmpHeap →
      st.regs 11 = eList.length → st.regs 12 = eListPtr →
      st.regs 13 = wstrNumPtr → st.regs 14 = wstrDenPtr → st.regs 15 = idx →
      ZeroFrom st.mem tmpHeap →
      (∀ z < tmpHeap, z < wtArr ∨ wtArr + eCap0 * L_in ≤ z → st.mem z = mem0 z) →
      (∀ e ∈ G₀.E,
        if e ∈ (eList.take idx).toFinset then
          Valid st.mem (wtArr + e * L_in) h L_in ∧
          0 < fixVal st.mem (wtArr + e * L_in) h L_in P_fp ∧
          (1 - 1 / (4 * (k_nat : ℝ))) * v_cur e * Real.exp (S_cur.wstr e / (rho_nat : ℝ)) ≤
            fixVal st.mem (wtArr + e * L_in) h L_in P_fp ∧
          fixVal st.mem (wtArr + e * L_in) h L_in P_fp ≤
            (1 + 1 / (4 * (k_nat : ℝ))) * v_cur e * Real.exp (S_cur.wstr e / (rho_nat : ℝ))
        else
          ∀ t < L_in, st.mem (wtArr + e * L_in + t) = mem0 (wtArr + e * L_in + t)) →
      ∃ st' c,
        Runs w p ω
          (.loop (.bin .lt (.reg 15) (.reg 11))
            ((.assign 16 (.load (.bin .add (.reg 12) (.reg 15))) ;;
              .assign 17 (.bin .add (.reg 13) (.bin .mul (.reg 16) (.reg 6))) ;;
              .assign 18 (.bin .add (.reg 14) (.bin .mul (.reg 16) (.reg 6))) ;;
              .assign 19 (.bin .add (.reg 2) (.bin .mul (.reg 16) (.reg 5))) ;;
              .call 20 bEdgeStep [.reg 17, .reg 18, .reg 19, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8]) ;;
             .assign 15 (.bin .add (.reg 15) (.const 1))))
          st .normal st' c ∧
        ZeroFrom st'.mem tmpHeap ∧
        (∀ z < tmpHeap, z < wtArr ∨ wtArr + eCap0 * L_in ≤ z → st'.mem z = mem0 z) ∧
        (∀ e ∈ G₀.E,
          Valid st'.mem (wtArr + e * L_in) h L_in ∧
          0 < fixVal st'.mem (wtArr + e * L_in) h L_in P_fp ∧
          (1 - 1 / (4 * (k_nat : ℝ))) * v_cur e * Real.exp (S_cur.wstr e / (rho_nat : ℝ)) ≤
            fixVal st'.mem (wtArr + e * L_in) h L_in P_fp ∧
          fixVal st'.mem (wtArr + e * L_in) h L_in P_fp ≤
            (1 + 1 / (4 * (k_nat : ℝ))) * v_cur e * Real.exp (S_cur.wstr e / (rho_nat : ℝ))) ∧
        c ≤ (eList.length - idx) * (mwuEdgeStepCost L_in L_w P_fp + 80) + 10 := by
  have h2w_16 : 16 ≤ 2 ^ w := by
    have : 2 ^ 5 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  intro idx hidx
  obtain ⟨rem, hrem⟩ : ∃ rem, eList.length - idx = rem := ⟨_, rfl⟩
  induction rem generalizing idx with
  | zero =>
    intro st _ _ _ _ _ _ _ hr11 _ _ _ hr15 hz hfr hinv
    have hidx_eq : idx = eList.length := by omega
    refine ⟨st, 4, runs_loop_iff.mpr (Or.inl ⟨by
        simp [Expr.eval, BinOp.eval, hr15, hr11, hidx_eq, show 0 < 2 ^ w by omega],
      rfl, by simp [Expr.size]⟩), hz, hfr, ?_, by omega⟩
    intro e he
    have hmem_take : e ∈ (eList.take idx).toFinset := by
      rw [hidx_eq, List.take_length, List.mem_toFinset]; exact (heL_mem e).mpr he
    simpa only [ite_eq_left hmem_take] using hinv e he
  | succ rem ih =>
    intro st hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr11 hr12 hr13 hr14 hr15 hz hfr hinv
    have hidx_lt : idx < eList.length := by omega
    set e := eList[idx]'hidx_lt
    have he_mem : e ∈ G₀.E := (heL_mem e).mp (List.getElem_mem hidx_lt)
    have he_cap : e < eCap0 := he_lt e he_mem
    have he_not_take : e ∉ (eList.take idx).toFinset := by
      rw [List.mem_toFinset]
      intro hmem
      obtain ⟨j, hj_len, hj_eq⟩ := List.getElem_of_mem hmem
      rw [List.length_take, min_eq_left (by omega)] at hj_len
      rw [List.getElem_take] at hj_eq
      have := (List.Nodup.getElem_inj_iff heL_nd).mp hj_eq
      omega
    have he_wt_eq : ∀ t < L_in, st.mem (wtArr + e * L_in + t) = mem0 (wtArr + e * L_in + t) := by
      simpa only [ite_eq_right he_not_take] using hinv e he_mem
    have hread_e : st.mem (eListPtr + idx) = e := by
      rw [hfr (eListPtr + idx) (by omega) (by rcases heL_disj with h | h <;> [left; right] <;> omega)]
      exact heL_at idx hidx_lt
    have he_mul_Lw_le : (e + 1) * L_w ≤ eCap0 * L_w := Nat.mul_le_mul_right L_w (by omega)
    have he_mul_Lin_le : (e + 1) * L_in ≤ eCap0 * L_in := Nat.mul_le_mul_right L_in (by omega)
    have heLw_add : e * L_w + L_w = (e + 1) * L_w := by ring
    have heLin_add : e * L_in + L_in = (e + 1) * L_in := by ring
    set numP := wstrNumPtr + e * L_w
    set denP := wstrDenPtr + e * L_w
    set wtP := wtArr + e * L_in
    have hnum_eq : ∀ t < L_w, st.mem (numP + t) = mem0 (numP + t) := fun t ht =>
      hfr _ (by dsimp [numP]; omega) (by rcases hnum_disj with h | h <;> [left; right] <;> (dsimp [numP]; omega))
    have hden_eq : ∀ t < L_w, st.mem (denP + t) = mem0 (denP + t) := fun t ht =>
      hfr _ (by dsimp [denP]; omega) (by rcases hden_disj with h | h <;> [left; right] <;> (dsimp [denP]; omega))
    have hone_mem : ∀ t < L_w, st.mem (onePtr + t) = mem0 (onePtr + t) := fun t ht =>
      hfr _ (by omega) (by rcases hone_disj with h | h <;> [left; right] <;> omega)
    have hrho_mem : ∀ t < L_w, st.mem (rhoPtr + t) = mem0 (rhoPtr + t) := fun t ht =>
      hfr _ (by omega) (by rcases hrho_disj with h | h <;> [left; right] <;> omega)
    obtain ⟨hv_num0, hv_den0, hnum_pos0, hden_pos0, hwstr_eq0, hwstr_lo0, hwstr_hi0⟩ := hWstr e he_mem
    obtain ⟨hv_wt0, hv_eq0, hv_lo0, hv_hi0⟩ := hwt0 e he_mem
    have hstep_call := mwuEdgeStep_runs (p := p) (ω := ω) (pos := st.pos)
      (numPtr := numP) (denPtr := denP) (wtPtr := wtP)
      hh hw hLin_le hk hdiv hq_P hk_q hP_Lin hm_Lin h2P_ltw hrho_pos hrho_cap
      (by dsimp [numP]; omega) (by dsimp [denP]; omega) (by dsimp [wtP]; omega) hone_le hrho_le
      hsp hz
      (fun t ht => by rw [hnum_eq t ht]; exact hv_num0 t ht)
      (fun t ht => by rw [hden_eq t ht]; exact hv_den0 t ht)
      (fun t ht => by rw [he_wt_eq t ht]; exact hv_wt0 t ht)
      (fun t ht => by rw [hone_mem t ht]; exact hv_one t ht)
      (fun t ht => by rw [hrho_mem t ht]; exact hv_rho t ht)
      (by rw [intVal_congr hnum_eq]; exact hnum_pos0)
      (by rw [intVal_congr hden_eq]; exact hden_pos0)
      (by rw [intVal_congr hnum_eq, intVal_congr hden_eq]; exact hwstr_eq0)
      hwstr_lo0 hwstr_hi0
      (by unfold fixVal; rw [intVal_congr he_wt_eq]; exact hv_eq0)
      hv_lo0 hv_hi0
      ((intVal_congr hone_mem).trans hone_eq)
      ((intVal_congr hrho_mem).trans hrho_eq)
      hDiv hExp hMul hCopy hFill
    obtain ⟨st_c, c_c, hrun_c, hv_wt_c, hpos_c, hlb_c, hub_c, hfr_c, hz_c, hc_c⟩ := hstep_call
    -- Execute one body iteration
    have hstep : ∃ st1 c_b,
        Runs w p ω
          ((.assign 16 (.load (.bin .add (.reg 12) (.reg 15))) ;;
            .assign 17 (.bin .add (.reg 13) (.bin .mul (.reg 16) (.reg 6))) ;;
            .assign 18 (.bin .add (.reg 14) (.bin .mul (.reg 16) (.reg 6))) ;;
            .assign 19 (.bin .add (.reg 2) (.bin .mul (.reg 16) (.reg 5))) ;;
            .call 20 bEdgeStep [.reg 17, .reg 18, .reg 19, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8]) ;;
           .assign 15 (.bin .add (.reg 15) (.const 1)))
          st .normal st1 c_b ∧
        (∀ r ≤ 14, st1.regs r = st.regs r) ∧ st1.regs 15 = idx + 1 ∧
        st1.mem = st_c.mem ∧ c_b ≤ mwuEdgeStepCost L_in L_w P_fp + 75 := by
      suffices hs : ∃ o st1 c_b,
          Runs w p ω
            ((.assign 16 (.load (.bin .add (.reg 12) (.reg 15))) ;;
              .assign 17 (.bin .add (.reg 13) (.bin .mul (.reg 16) (.reg 6))) ;;
              .assign 18 (.bin .add (.reg 14) (.bin .mul (.reg 16) (.reg 6))) ;;
              .assign 19 (.bin .add (.reg 2) (.bin .mul (.reg 16) (.reg 5))) ;;
              .call 20 bEdgeStep [.reg 17, .reg 18, .reg 19, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8]) ;;
             .assign 15 (.bin .add (.reg 15) (.const 1)))
            st o st1 c_b ∧
          (o = .normal ∧ (∀ r ≤ 14, st1.regs r = st.regs r) ∧ st1.regs 15 = idx + 1 ∧
            st1.mem = st_c.mem) ∧
          0 + c_b ≤ mwuEdgeStepCost L_in L_w P_fp + 75 by
        rcases hs with ⟨_, st1, c_b, hrun, ⟨rfl, h1, h2, h3⟩, hc⟩
        exact ⟨st1, c_b, hrun, h1, h2, h3, by omega⟩
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := e)
        (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr12, hr15, show eListPtr + idx < 2 ^ w by omega])
          hread_e) ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := numP)
        (by dsimp only [numP]
            simp [Expr.eval, BinOp.eval, hr13, hr6, show e * L_w < 2 ^ w by omega,
              show wstrNumPtr + e * L_w < 2 ^ w by omega]) ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := denP)
        (by dsimp only [denP]
            simp [Expr.eval, BinOp.eval, hr14, hr6, show e * L_w < 2 ^ w by omega,
              show wstrDenPtr + e * L_w < 2 ^ w by omega]) ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := wtP)
        (by dsimp only [wtP]
            simp [Expr.eval, BinOp.eval, hr2, hr5, show e * L_in < 2 ^ w by omega,
              show wtArr + e * L_in < 2 ^ w by omega]) ?_
      have hcall_eval : evalArgs w
          { mem := st.mem,
            regs := Function.update (Function.update (Function.update (Function.update st.regs 16 e) 17 numP) 18 denP) 19 wtP,
            pos := st.pos }
          [.reg 17, .reg 18, .reg 19, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8] =
          some [numP, denP, wtP, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] := by
        simp [evalArgs, Expr.eval, hr3, hr4, hr5, hr6, hr7, hr8]
      have hcall_run : Runs w p ω
          (.call 20 bEdgeStep [.reg 17, .reg 18, .reg 19, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8])
          { mem := st.mem,
            regs := Function.update (Function.update (Function.update (Function.update st.regs 16 e) 17 numP) 18 denP) 19 wtP,
            pos := st.pos }
          .normal
          { mem := st_c.mem,
            regs := Function.update (Function.update (Function.update (Function.update (Function.update st.regs 16 e) 17 numP) 18 denP) 19 wtP) 20 0,
            pos := st_c.pos }
          (argsSize [.reg 17, .reg 18, .reg 19, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8] + c_c + 1) := by
        rw [runs_call_iff]
        exact ⟨[numP, denP, wtP, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap],
          mwuEdgeStepProc bDiv bExp bMul bCopy bFill, .returned 0, st_c, c_c,
          hcall_eval, hpStep, hrun_c, rfl, rfl, rfl⟩
      refine runs_seq_of_runs' hcall_run ?_
      refine runs_assign_le (v := idx + 1)
        (by simp [Expr.eval, BinOp.eval, hr15, show 1 < 2 ^ w by omega, show idx + 1 < 2 ^ w by omega])
        ⟨rfl, fun r hr => by
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
         by simp, rfl⟩ ?_
      dsimp only [argsSize, Expr.size]
      omega
    obtain ⟨st1, c_b, hrun_b, hr1_lo, hr1_15, hmem1, hcb⟩ := hstep
    have hfr1 : ∀ z < tmpHeap, z < wtArr ∨ wtArr + eCap0 * L_in ≤ z → st1.mem z = mem0 z := fun z hzt hzw => by
      rw [hmem1, hfr_c z hzt (by rcases hzw with h | h <;> [left; right] <;> (dsimp [wtP]; omega))]
      exact hfr z hzt hzw
    have hinv1 : ∀ f ∈ G₀.E,
        if f ∈ (eList.take (idx + 1)).toFinset then
          Valid st1.mem (wtArr + f * L_in) h L_in ∧
          0 < fixVal st1.mem (wtArr + f * L_in) h L_in P_fp ∧
          (1 - 1 / (4 * (k_nat : ℝ))) * v_cur f * Real.exp (S_cur.wstr f / (rho_nat : ℝ)) ≤
            fixVal st1.mem (wtArr + f * L_in) h L_in P_fp ∧
          fixVal st1.mem (wtArr + f * L_in) h L_in P_fp ≤
            (1 + 1 / (4 * (k_nat : ℝ))) * v_cur f * Real.exp (S_cur.wstr f / (rho_nat : ℝ))
        else
          ∀ t < L_in, st1.mem (wtArr + f * L_in + t) = mem0 (wtArr + f * L_in + t) := by
      intro f hf
      have hf_cap : f < eCap0 := he_lt f hf
      have htake_eq : f ∈ (eList.take (idx + 1)).toFinset ↔ f ∈ (eList.take idx).toFinset ∨ f = e := by
        rw [List.take_add_one, List.getElem?_eq_getElem hidx_lt]
        simp only [e, Option.toList_some, List.toFinset_append, List.toFinset_cons,
          List.toFinset_nil, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
      by_cases hfe : f = e
      · subst hfe
        rw [ite_eq_left (htake_eq.mpr (Or.inr rfl)), hmem1]
        exact ⟨hv_wt_c, hpos_c, hlb_c, hub_c⟩
      · have hdisj_f : ∀ t < L_in, st1.mem (wtArr + f * L_in + t) = st.mem (wtArr + f * L_in + t) := by
          intro t ht
          have hne_slot : wtArr + f * L_in + t < wtP ∨ wtP + L_in ≤ wtArr + f * L_in + t := by
            dsimp only [wtP]
            rcases Nat.lt_or_gt_of_ne hfe with hlt | hgt
            · left
              have : (f + 1) * L_in ≤ e * L_in := Nat.mul_le_mul_right L_in (by omega)
              have : f * L_in + L_in = (f + 1) * L_in := by ring
              omega
            · right
              have : (e + 1) * L_in ≤ f * L_in := Nat.mul_le_mul_right L_in (by omega)
              have : e * L_in + L_in = (e + 1) * L_in := by ring
              omega
          have hf_mul_le : (f + 1) * L_in ≤ eCap0 * L_in := Nat.mul_le_mul_right L_in (by omega)
          have hf_add : f * L_in + L_in = (f + 1) * L_in := by ring
          rw [hmem1]
          exact hfr_c _ (by omega) hne_slot
        by_cases hmem_prev : f ∈ (eList.take idx).toFinset
        · rw [ite_eq_left (htake_eq.mpr (Or.inl hmem_prev))]
          have hp := hinv f hf
          rw [ite_eq_left hmem_prev] at hp
          have hfix_eq : fixVal st1.mem (wtArr + f * L_in) h L_in P_fp =
              fixVal st.mem (wtArr + f * L_in) h L_in P_fp := by
            unfold fixVal; rw [intVal_congr hdisj_f]
          rw [hfix_eq]
          exact ⟨fun t ht => by rw [hdisj_f t ht]; exact hp.1 t ht, hp.2⟩
        · have hnot_next : f ∉ (eList.take (idx + 1)).toFinset := by
            rw [htake_eq]; push Not; exact ⟨hmem_prev, hfe⟩
          rw [ite_eq_right hnot_next]
          have hp := hinv f hf
          rw [ite_eq_right hmem_prev] at hp
          intro t ht
          exact (hdisj_f t ht).trans (hp t ht)
    obtain ⟨st', c_r, hrun_r, hz', hfr', hinv', hcr⟩ := ih (idx + 1) (by omega) (by omega) st1
      ((hr1_lo 2 (by decide)).trans hr2) ((hr1_lo 3 (by decide)).trans hr3)
      ((hr1_lo 4 (by decide)).trans hr4) ((hr1_lo 5 (by decide)).trans hr5)
      ((hr1_lo 6 (by decide)).trans hr6) ((hr1_lo 7 (by decide)).trans hr7)
      ((hr1_lo 8 (by decide)).trans hr8) ((hr1_lo 11 (by decide)).trans hr11)
      ((hr1_lo 12 (by decide)).trans hr12) ((hr1_lo 13 (by decide)).trans hr13)
      ((hr1_lo 14 (by decide)).trans hr14) hr1_15 (hmem1 ▸ hz_c) hfr1 hinv1
    refine ⟨st', 3 + c_b + c_r + 1, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, c_b, c_r,
      by simp [Expr.eval, BinOp.eval, hr15, hr11, hidx_lt, show 1 < 2 ^ w by omega],
      by decide, hrun_b, hrun_r, by simp [Expr.size]⟩)), hz', hfr', hinv', ?_⟩
    have hmul : (rem + 1) * (mwuEdgeStepCost L_in L_w P_fp + 80) =
        rem * (mwuEdgeStepCost L_in L_w P_fp + 80) + (mwuEdgeStepCost L_in L_w P_fp + 80) := by ring
    rw [show eList.length - (idx + 1) = rem by omega] at hcr
    rw [hrem, hmul]
    omega

lemma mwuWeightsLoop_runs {w h q bEdgeStep bDiv bExp bMul bCopy bFill
    g0Ptr lsfHandle wtArr onePtr rhoPtr L_in L_w P_fp tmpHeap k_nat rho_nat vCap0 eCap0 : ℕ}
    {G₀ : MGraph} {S_cur : LSFState} {x_cur : LSFConcrete} {v_cur : ℕ → ℝ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    (hh : 1 ≤ h) (hw : 3 * h + 2 ≤ w) (hLin_le : L_in ≤ L_w) (hk : 1 ≤ k_nat)
    (hdiv : h ∣ P_fp) (hq_P : q + 11 ≤ P_fp) (hk_q : 8 * k_nat ≤ 2 ^ q)
    (hP_Lin : P_fp + 6 ≤ h * L_in)
    (hm_Lin : 32 * (G₀.E.card + 1) * 2 ^ P_fp < 2 ^ (h * L_in - 1))
    (h2P_ltw : 2 * P_fp + 9 < 2 ^ w)
    (hrho_pos : 1 ≤ rho_nat) (hrho_cap : rho_nat < 2 ^ (h * (L_w - L_in)))
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hrep : (LSFRep h).rep lsfHandle S_cur x_cur mem)
    (hS_G : S_cur.G = G₀) (hLw_eq : x_cur.L_w = L_w)
    (hwstr_bds : ∀ e ∈ G₀.E, 1 ≤ S_cur.wstr e ∧ S_cur.wstr e ≤ (rho_nat : ℝ) / 10)
    (hwt0 : ∀ e ∈ G₀.E,
      Valid mem (wtArr + e * L_in) h L_in ∧
      fixVal mem (wtArr + e * L_in) h L_in P_fp = v_cur e ∧
      (1 / 2 : ℝ) ≤ v_cur e ∧ v_cur e ≤ 8 * (G₀.E.card : ℝ))
    (hg0_le : g0Ptr + dynGraphSize vCap0 eCap0 ≤ wtArr)
    (hwt_le : wtArr + x_cur.eCap * L_in ≤ onePtr)
    (heCap_le : eCap0 ≤ x_cur.eCap)
    (hone_le : onePtr + L_w ≤ rhoPtr)
    (hrho_le : rhoPtr + L_w ≤ lsfHandle)
    (hend_le : x_cur.endAddr lsfHandle ≤ tmpHeap)
    (hsp : tmpHeap + mwuEdgeStepSpace L_in L_w P_fp < 2 ^ w)
    (hz : ZeroFrom mem tmpHeap)
    (hv_one : Valid mem onePtr h L_w) (hone_eq : intVal mem onePtr h L_w = (2 : ℤ) ^ P_fp)
    (hv_rho : Valid mem rhoPtr h L_w) (hrho_eq : intVal mem rhoPtr h L_w = (rho_nat : ℤ) * (2 : ℤ) ^ P_fp)
    (hpStep : p.procs[bEdgeStep]? = some (mwuEdgeStepProc bDiv bExp bMul bCopy bFill))
    (hDiv : MeetsContract w p bDiv (fixedDivideContract w h))
    (hExp : MeetsContract w p bExp (positiveExponentialContract w h q))
    (hMul : MeetsContract w p bMul (fixedMultiplyContract w h))
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hFill : MeetsContract w p bFill (memFillContract w)) :
    ∃ st' c,
      Runs w p ω (mwuWeightsLoopProc bEdgeStep)
        (startState [g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos)
        (.returned 0) st' c ∧
      ZeroFrom st'.mem tmpHeap ∧
      (∀ z < tmpHeap, z < wtArr ∨ wtArr + eCap0 * L_in ≤ z → st'.mem z = mem z) ∧
      (∀ e ∈ G₀.E,
        Valid st'.mem (wtArr + e * L_in) h L_in ∧
        0 < fixVal st'.mem (wtArr + e * L_in) h L_in P_fp ∧
        (1 - 1 / (4 * (k_nat : ℝ))) * v_cur e * Real.exp (S_cur.wstr e / (rho_nat : ℝ)) ≤
          fixVal st'.mem (wtArr + e * L_in) h L_in P_fp ∧
        fixVal st'.mem (wtArr + e * L_in) h L_in P_fp ≤
          (1 + 1 / (4 * (k_nat : ℝ))) * v_cur e * Real.exp (S_cur.wstr e / (rho_nat : ℝ))) ∧
      c ≤ G₀.E.card * (mwuEdgeStepCost L_in L_w P_fp + 80) + 120 := by
  have h2w_16 : 16 ≤ 2 ^ w := by
    have : 2 ^ 5 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hxH : x_cur.h = h := hrep.1
  have hhdr := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwstrAt := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  set numPtr := lsfWstrNumPtr lsfHandle x_cur.vCap x_cur.eCap x_cur.n0 x_cur.tM
  set denPtr := lsfWstrDenPtr lsfHandle x_cur.vCap x_cur.eCap x_cur.n0 x_cur.tM x_cur.L_w
  have hhdr_num : mem (lsfHandle + lsfOffWstrNumPtr) = numPtr := hhdr.2.2.2.2.2.2.2.2.2.1
  have hhdr_den : mem (lsfHandle + lsfOffWstrDenPtr) = denPtr := hhdr.2.2.2.2.2.2.2.2.2.2.1
  have hnum_ge : lsfHandle ≤ numPtr := by
    dsimp [numPtr, lsfWstrNumPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  have hden_ge : lsfHandle ≤ denPtr := by
    dsimp [denPtr, lsfWstrDenPtr, lsfWstrNumPtr, lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  have hnum_end : numPtr + x_cur.eCap * L_w ≤ x_cur.endAddr lsfHandle := by
    rw [← hLw_eq]
    dsimp [LSFConcrete.endAddr, lsfEndAddr, lsfStaticSize, numPtr, lsfWstrNumPtr, lsfWBlockPtr,
      lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  have hden_end : denPtr + x_cur.eCap * L_w ≤ x_cur.endAddr lsfHandle := by
    rw [← hLw_eq]
    dsimp [LSFConcrete.endAddr, lsfEndAddr, lsfStaticSize, denPtr, lsfWstrDenPtr, lsfWstrNumPtr,
      lsfWBlockPtr, lsfFAncPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr]; omega
  have hhdr_end : lsfHandle + lsfHdrSize ≤ x_cur.endAddr lsfHandle :=
    lsfHdr_lt_end lsfHandle x_cur.vCap x_cur.eCap x_cur.n0 x_cur.tM x_cur.L_w
  have heCap_mul_in : eCap0 * L_in ≤ x_cur.eCap * L_in := Nat.mul_le_mul_right L_in heCap_le
  have heCap_mul_w : eCap0 * L_w ≤ x_cur.eCap * L_w := Nat.mul_le_mul_right L_w heCap_le
  obtain ⟨eL, heL_len, heL_nd, heL_mem, heL_at, _⟩ := hdg0.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvCap0_m : mem (g0Ptr + dgVCapOff) = vCap0 := hdg0.2.2.2.1
  have heCap0_m : mem (g0Ptr + dgECapOff) = eCap0 := hdg0.2.2.2.2.1
  have hm0_m : mem (g0Ptr + dgMOff) = G₀.E.card := hdg0.2.2.2.2.2.2.1
  have hm0_le : G₀.E.card ≤ eCap0 := (dynGraph_card_le hdg0).2
  have heL_end : dgEListBase g0Ptr vCap0 eCap0 + G₀.E.card ≤ g0Ptr + dynGraphSize vCap0 eCap0 := by
    dsimp [dgEListBase, dynGraphSize]; omega
  have hWstr_ok : ∀ e ∈ G₀.E,
      Valid mem (numPtr + e * L_w) h L_w ∧ Valid mem (denPtr + e * L_w) h L_w ∧
      0 < intVal mem (numPtr + e * L_w) h L_w ∧ 0 < intVal mem (denPtr + e * L_w) h L_w ∧
      (intVal mem (numPtr + e * L_w) h L_w : ℝ) / (intVal mem (denPtr + e * L_w) h L_w : ℝ) =
        S_cur.wstr e ∧
      1 ≤ S_cur.wstr e ∧ S_cur.wstr e ≤ (rho_nat : ℝ) / 10 := by
    intro e he
    have heS : e ∈ S_cur.G.E := hS_G ▸ he
    obtain ⟨_, hvn, hvd, hnn, hdp, hrat⟩ := hwstrAt.2.2 e heS
    rw [hxH, hLw_eq] at hvn hvd hnn hdp hrat
    obtain ⟨hlo, hhi⟩ := hwstr_bds e he
    exact ⟨hvn, hvd, by omega, by omega, hrat, hlo, hhi⟩
  suffices hmain : ∃ o st' c,
      Runs w p ω (mwuWeightsLoopProc bEdgeStep)
        (startState [g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos)
        o st' c ∧
      (o = .returned 0 ∧ ZeroFrom st'.mem tmpHeap ∧
        (∀ z < tmpHeap, z < wtArr ∨ wtArr + eCap0 * L_in ≤ z → st'.mem z = mem z) ∧
        (∀ e ∈ G₀.E,
          Valid st'.mem (wtArr + e * L_in) h L_in ∧
          0 < fixVal st'.mem (wtArr + e * L_in) h L_in P_fp ∧
          (1 - 1 / (4 * (k_nat : ℝ))) * v_cur e * Real.exp (S_cur.wstr e / (rho_nat : ℝ)) ≤
            fixVal st'.mem (wtArr + e * L_in) h L_in P_fp ∧
          fixVal st'.mem (wtArr + e * L_in) h L_in P_fp ≤
            (1 + 1 / (4 * (k_nat : ℝ))) * v_cur e * Real.exp (S_cur.wstr e / (rho_nat : ℝ)))) ∧
      0 + c ≤ G₀.E.card * (mwuEdgeStepCost L_in L_w P_fp + 80) + 120 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2, h3⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, h3, by omega⟩
  have hr0 : (startState [g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 0 = g0Ptr := by simp [startState]
  have hr1 : (startState [g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 1 = lsfHandle := by simp [startState]
  have hr2 : (startState [g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 2 = wtArr := by simp [startState]
  have hr3 : (startState [g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 3 = onePtr := by simp [startState]
  have hr4 : (startState [g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 4 = rhoPtr := by simp [startState]
  have hr5 : (startState [g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 5 = L_in := by simp [startState]
  have hr6 : (startState [g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 6 = L_w := by simp [startState]
  have hr7 : (startState [g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 7 = P_fp := by simp [startState]
  have hr8 : (startState [g0Ptr, lsfHandle, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 8 = tmpHeap := by simp [startState]
  dsimp only [mwuWeightsLoopProc]
  refine runs_seq_assign_le (v := vCap0)
    (Expr.eval_load_of_eq (by
      have : g0Ptr + dgVCapOff < 2 ^ w := by dsimp [dgVCapOff, dynGraphSize] at hg0_le ⊢; omega
      simp [Expr.eval, BinOp.eval, hr0, show dgVCapOff < 2 ^ w by dsimp [dgVCapOff]; omega, this]) hvCap0_m) ?_
  refine runs_seq_assign_le (v := eCap0)
    (Expr.eval_load_of_eq (by
      have : g0Ptr + dgECapOff < 2 ^ w := by dsimp [dgECapOff, dynGraphSize] at hg0_le ⊢; omega
      simp [Expr.eval, BinOp.eval, hr0, show dgECapOff < 2 ^ w by dsimp [dgECapOff]; omega, this]) heCap0_m) ?_
  refine runs_seq_assign_le (v := G₀.E.card)
    (Expr.eval_load_of_eq (by
      have : g0Ptr + dgMOff < 2 ^ w := by dsimp [dgMOff, dynGraphSize] at hg0_le ⊢; omega
      simp [Expr.eval, BinOp.eval, hr0, show dgMOff < 2 ^ w by dsimp [dgMOff]; omega, this]) hm0_m) ?_
  refine runs_seq_assign_le (v := dgEListBase g0Ptr vCap0 eCap0)
    (by dsimp only [dgEListBase]
        have hdg_sz : g0Ptr + 4 + 7 * vCap0 + eCap0 < 2 ^ w := by
          dsimp [dynGraphSize] at hg0_le; omega
        simp [Expr.eval, BinOp.eval, hr0, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
          show g0Ptr + 4 < 2 ^ w by omega, show 7 * vCap0 < 2 ^ w by omega,
          show g0Ptr + 4 + 7 * vCap0 < 2 ^ w by omega, hdg_sz]) ?_
  refine runs_seq_assign_le (v := numPtr)
    (Expr.eval_load_of_eq (by
      have h1 : lsfOffWstrNumPtr < 2 ^ w := by dsimp [lsfOffWstrNumPtr]; omega
      have h2 : lsfHandle + lsfOffWstrNumPtr < 2 ^ w := by
        dsimp [lsfOffWstrNumPtr, lsfHdrSize] at hhdr_end ⊢; omega
      simp [Expr.eval, BinOp.eval, hr1, h1, h2]) hhdr_num) ?_
  refine runs_seq_assign_le (v := denPtr)
    (Expr.eval_load_of_eq (by
      have h1 : lsfOffWstrDenPtr < 2 ^ w := by dsimp [lsfOffWstrDenPtr]; omega
      have h2 : lsfHandle + lsfOffWstrDenPtr < 2 ^ w := by
        dsimp [lsfOffWstrDenPtr, lsfHdrSize] at hhdr_end ⊢; omega
      simp [Expr.eval, BinOp.eval, hr1, h1, h2]) hhdr_den) ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_
  refine runs_seq_of_exists'
    (mwuWeightsInner_runs (bEdgeStep := bEdgeStep) (eListPtr := dgEListBase g0Ptr vCap0 eCap0)
      (wstrNumPtr := numPtr) (wstrDenPtr := denPtr)
      (mem0 := mem) (p := p) (ω := ω)
      hh hw hLin_le hk hdiv hq_P hk_q hP_Lin hm_Lin h2P_ltw hrho_pos hrho_cap
      hpStep hDiv hExp hMul hCopy hFill
      heL_len heL_nd heL_mem heL_at hdg0.2.2.1 (by omega) (Or.inl (by omega))
      (by omega) (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))
      (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))
      hsp hv_one hone_eq hv_rho hrho_eq hWstr_ok hwt0
      0 (Nat.zero_le _) _
      (by simp [hr2]) (by simp [hr3]) (by simp [hr4]) (by simp [hr5]) (by simp [hr6])
      (by simp [hr7]) (by simp [hr8]) (by simp [heL_len, MGraph.m]) (by simp) (by simp) (by simp) (by simp)
      hz (fun _ _ _ => rfl) (fun _ _ => by simp [List.take_zero, startState])) ?_
  intro st_end c_loop ⟨hz_end, hfr_end, hinv_end, hc_loop⟩
  refine runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega])
    ⟨rfl, hz_end, hfr_end, hinv_end⟩ ?_
  rw [heL_len, Nat.sub_zero] at hc_loop
  dsimp only [MGraph.m, Expr.size] at hc_loop ⊢
  omega

end

end MinCostFlow.LSF.Program
