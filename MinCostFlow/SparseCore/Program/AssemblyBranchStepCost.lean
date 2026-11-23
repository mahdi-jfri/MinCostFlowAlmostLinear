module

public import MinCostFlow.SparseCore.Program.AssemblyBranchStep
public import MinCostFlow.SparseCore.Program.ReadChangeBound
import Mathlib.Tactic.Ring

/-!
# The cost of the step of a branch in the form of the clause (`AssemblyBranchStepCost`)

`asmBrFull_step_runs` (`AssemblyBranchStep.lean`) bounds the cost of the step of a branch by four
terms: the charge of the first phase, P7's output step, P10's update and `150`. The clause
`step_runs` of `AsmBranchAt` asks the cost `S.mul · (charge + (words + editWords + 1) · lg)`, with
`charge = branchStepCharge …` and `lg = bundleLogFactor M N = (log₂ (M + N + 2) + 1) ^ 2`. This
file reduces the four terms to that form (`asmBrStep_cost_le`) and restates the step with it
(`asmBrFull_step_runs_clauseCost`).

**The route.** Write `l = log₂ (M + N + 2) + 1`, so `lg = l²`, and `Q = charge + W · lg` with
`W = words + editWords + 1`.
* P7's step costs a constant times `(Enc + ysMul (Enc + W) l + 1) · ordStoreLog eCap`, where
  `Enc` is the size of the output batch `U_S`. The order store has `ordStoreLog eCap ≤
  (capExp + 1) · l`, since `eCap + 2 ≤ (M + N + 2) ^ capExp` (`ordStoreLog_le_of_cap`,
  `AssemblyWordSize.lean`). So the term is at most a constant times `Enc · lg + (Enc + W) · lg +
  lg`. The charge of the model has the term `Enc · lg` (`branchStepCharge_ge`), so this is at most
  `(ysMul + 1) · Q`.
* P10's update costs `readMul · ((words + usWords + 1) · (L_w + 1) + c.size)` (the clause
  `ReadBranchAt.step`), with `usWords ≤ 5 Enc + 1`. The limb count has `L_w + 1 ≤ (limbMul + capExp
  + 129) · lg`, from the limb bound of the representation and `L ≤ limbMul · lg` (`limbs_succ_le`).
  The change record of P4 has `c.size ≤ 112 capExp² · charge` on the model
  (`lsfChangeSize_le_capExp_branchStepCharge`, `ReadChangeBound.lean`). So the term is at most
  `readMul · (5 (limbMul + capExp + 129) + 112 capExp²) · Q`.
* The first phase costs `J.mul · Q`, and `150 ≤ 150 · Q`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Read

/-- **The limb count is paid by the log factor**: from the limb bound of readout `2` and
`L ≤ limbMul · lg`, `L_w + 1 ≤ (limbMul + capExp + 129) · lg`. -/
theorem limbs_succ_le {L_w L M N capExp limbMul : ℕ}
    (hL : L ≤ limbMul * bundleLogFactor M N)
    (hLw : L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)) :
    L_w + 1 ≤ (limbMul + capExp + sparseCoreReadout2LimbConst + 1) * bundleLogFactor M N := by
  set l := Nat.log 2 (M + N + 2) + 1
  have hlg : bundleLogFactor M N = l * l := by unfold bundleLogFactor; ring
  have hl1 : 1 ≤ l := by omega
  have hll : l ≤ l * l := Nat.le_mul_of_pos_left l (by omega)
  have h1 := Nat.mul_le_mul_left (capExp + sparseCoreReadout2LimbConst) hll
  have h2 : (limbMul + capExp + sparseCoreReadout2LimbConst + 1) * (l * l) =
      limbMul * (l * l) + (capExp + sparseCoreReadout2LimbConst) * (l * l) + l * l := by ring
  have h3 : 1 ≤ l * l := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [hlg] at hL ⊢
  omega

/-- The charge of a step has the term `Enc(U_S) · lg`. -/
theorem branchStepCharge_ge {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    tr.S_cur.batchEnc (stepBundleTree sparsify tr U ord ord').U_S *
        bundleLogFactor tr.m₀ tr.n₀ ≤ branchStepCharge sparsify tr U ord ord' := by
  unfold branchStepCharge
  exact Nat.mul_le_mul_right _ (by omega)

/-- The output order-edit word-count multiplier for one branch step: `5 * ysMul + 10`. -/
def asmBrEdMul (ysMul : ℕ) : ℕ := 5 * ysMul + 10

/-- Bounding the output order-edit word count by `asmBrEdMul ysMul` times the branch step charge
plus `(words + editWords + 1) * bundleLogFactor M N`. -/
theorem asmBrStep_eW_le {ysMul charge words editWords Enc M N eW : ℕ}
    (heW : eW ≤ 5 * (2 * Enc + ysMul * (Enc + words + editWords + 1) *
      (Nat.log 2 (M + N + 2) + 1)) + 1)
    (hEnc : Enc * bundleLogFactor M N ≤ charge) :
    eW ≤ asmBrEdMul ysMul * (charge + (words + editWords + 1) * bundleLogFactor M N) := by
  set l := Nat.log 2 (M + N + 2) + 1
  set lg := bundleLogFactor M N
  set W := words + editWords + 1
  have hlg : lg = l * l := by show bundleLogFactor M N = l * l; unfold bundleLogFactor; ring
  have hl1 : 1 ≤ l := by omega
  have hlg1 : 1 ≤ lg := by rw [hlg]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hllg : l ≤ lg := by rw [hlg]; exact Nat.le_mul_of_pos_left l (by omega)
  have hEnc1 : Enc ≤ Enc * lg := Nat.le_mul_of_pos_right Enc (by omega)
  have hEncL : Enc * l ≤ Enc * lg := Nat.mul_le_mul_left Enc hllg
  have hWL : W * l ≤ W * lg := Nat.mul_le_mul_left W hllg
  have hW1 : 1 ≤ W * lg := le_trans hlg1 (Nat.le_mul_of_pos_left lg (by omega))
  have h1 : 5 * (2 * Enc + ysMul * (Enc + W) * l) + 1 =
      10 * Enc + 5 * ysMul * (Enc * l) + 5 * ysMul * (W * l) + 1 := by ring
  have h2 : asmBrEdMul ysMul * (charge + W * lg) =
      10 * charge + 5 * ysMul * charge + 5 * ysMul * (W * lg) + 10 * (W * lg) := by
    unfold asmBrEdMul; ring
  have h3 : 5 * ysMul * (Enc * l) ≤ 5 * ysMul * charge :=
    Nat.mul_le_mul_left _ (hEncL.trans hEnc)
  have h4 : 5 * ysMul * (W * l) ≤ 5 * ysMul * (W * lg) := Nat.mul_le_mul_left _ hWL
  have h5 : 10 * Enc ≤ 10 * charge := Nat.mul_le_mul_left 10 (hEnc1.trans hEnc)
  rw [show Enc + words + editWords + 1 = Enc + W by omega] at heW
  omega

/-- The cost multiplier of the step of a branch in the form of the clause: the first phase, P7's
step through the order store, P10's update with its limbs and the change record, and `150`. -/
def asmBrStepMul (jMul ysMul mulOut outMul readMul capExp limbMul : ℕ) : ℕ :=
  jMul + mulOut * (outMul + 1) * (capExp + 1) * (ysMul + 1) +
    readMul * (5 * (limbMul + capExp + sparseCoreReadout2LimbConst + 1) + 112 * capExp ^ 2) + 150

/-- **The cost of the step in the form of the clause.** The four terms of the cost of the step of
a branch (`asmBrFull_step_runs`) add up to at most `asmBrStepMul · (charge + W · lg)`; see the
module docstring. -/
theorem asmBrStep_cost_le {jMul ysMul mulOut outMul readMul capExp limbMul : ℕ}
    {charge words editWords Enc chgSize L_w L M N eCap : ℕ}
    (hEnc : Enc * bundleLogFactor M N ≤ charge)
    (hcs : chgSize ≤ 112 * capExp ^ 2 * charge)
    (hcap : eCap + 2 ≤ (M + N + 2) ^ capExp)
    (hL : L ≤ limbMul * bundleLogFactor M N)
    (hLw : L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)) :
    jMul * (charge + (words + editWords + 1) * bundleLogFactor M N) +
        mulOut * (outMul + 1) *
          (Enc + ysMul * (Enc + words + editWords + 1) * (Nat.log 2 (M + N + 2) + 1) + 1) *
          ordStoreLog eCap +
        readMul * ((words + (5 * Enc + 1) + 1) * (L_w + 1) + chgSize) + 150 ≤
      asmBrStepMul jMul ysMul mulOut outMul readMul capExp limbMul *
        (charge + (words + editWords + 1) * bundleLogFactor M N) := by
  have hO : ordStoreLog eCap ≤ (capExp + 1) * (Nat.log 2 (M + N + 2) + 1) :=
    (ordStoreLog_le_of_cap hcap).trans (Nat.mul_le_mul_right _ (by omega))
  have hLw1 := limbs_succ_le hL hLw
  set l := Nat.log 2 (M + N + 2) + 1
  set lg := bundleLogFactor M N
  set W := words + editWords + 1
  set Q := charge + W * lg
  set KL := limbMul + capExp + sparseCoreReadout2LimbConst + 1
  have hlg : lg = l * l := by show bundleLogFactor M N = l * l; unfold bundleLogFactor; ring
  have hl1 : 1 ≤ l := by omega
  have hlg1 : 1 ≤ lg := by rw [hlg]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hllg : l ≤ lg := by rw [hlg]; exact Nat.le_mul_of_pos_left l (by omega)
  have hWlg : lg ≤ W * lg := Nat.le_mul_of_pos_left lg (by omega)
  have hEncQ : Enc * lg ≤ charge := hEnc
  -- P7's step
  have hX : (Enc + ysMul * (Enc + W) * l + 1) * l ≤ (ysMul + 1) * Q := by
    have e1 : (Enc + ysMul * (Enc + W) * l + 1) * l =
        Enc * l + ysMul * (Enc * lg) + ysMul * (W * lg) + l := by rw [hlg]; ring
    have e2 : Enc * l ≤ Enc * lg := Nat.mul_le_mul_left _ hllg
    have e3 : ysMul * (Enc * lg) ≤ ysMul * charge := Nat.mul_le_mul_left _ hEncQ
    have e4 : (ysMul + 1) * Q = ysMul * charge + ysMul * (W * lg) + charge + W * lg := by ring
    rw [e1]
    omega
  have hT2 : mulOut * (outMul + 1) * (Enc + ysMul * (Enc + W) * l + 1) * ordStoreLog eCap ≤
      mulOut * (outMul + 1) * (capExp + 1) * (ysMul + 1) * Q := by
    calc mulOut * (outMul + 1) * (Enc + ysMul * (Enc + W) * l + 1) * ordStoreLog eCap
        ≤ mulOut * (outMul + 1) * (Enc + ysMul * (Enc + W) * l + 1) * ((capExp + 1) * l) :=
          Nat.mul_le_mul_left _ hO
      _ = mulOut * (outMul + 1) * (capExp + 1) * ((Enc + ysMul * (Enc + W) * l + 1) * l) := by
          ring
      _ ≤ mulOut * (outMul + 1) * (capExp + 1) * ((ysMul + 1) * Q) := Nat.mul_le_mul_left _ hX
      _ = mulOut * (outMul + 1) * (capExp + 1) * (ysMul + 1) * Q := by ring
  -- P10's update
  have hT3 : readMul * ((words + (5 * Enc + 1) + 1) * (L_w + 1) + chgSize) ≤
      readMul * (5 * KL + 112 * capExp ^ 2) * Q := by
    have e1 : (words + (5 * Enc + 1) + 1) * (L_w + 1) ≤ 5 * KL * Q := by
      calc (words + (5 * Enc + 1) + 1) * (L_w + 1) ≤ (words + (5 * Enc + 1) + 1) * (KL * lg) :=
            Nat.mul_le_mul_left _ hLw1
        _ = KL * (words * lg + 5 * (Enc * lg) + 2 * lg) := by ring
        _ ≤ KL * (5 * Q) := by
            refine Nat.mul_le_mul_left _ ?_
            have : (words + 2) * lg ≤ 2 * (W * lg) := by
              rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
            have e : (words + 2) * lg = words * lg + 2 * lg := by ring
            omega
        _ = 5 * KL * Q := by ring
    have e2 : chgSize ≤ (112 * capExp ^ 2) * Q := hcs.trans (Nat.mul_le_mul_left _ (by omega))
    calc readMul * ((words + (5 * Enc + 1) + 1) * (L_w + 1) + chgSize)
        ≤ readMul * (5 * KL * Q + (112 * capExp ^ 2) * Q) := Nat.mul_le_mul_left _ (by omega)
      _ = readMul * (5 * KL + 112 * capExp ^ 2) * Q := by ring
  have hQ1 : 1 ≤ Q := le_trans hlg1 (le_trans hWlg (by omega))
  have e : asmBrStepMul jMul ysMul mulOut outMul readMul capExp limbMul * Q =
      jMul * Q + mulOut * (outMul + 1) * (capExp + 1) * (ysMul + 1) * Q +
        readMul * (5 * KL + 112 * capExp ^ 2) * Q + 150 * Q := by
    unfold asmBrStepMul; ring
  have hW : ysMul * (Enc + words + editWords + 1) = ysMul * (Enc + W) := by
    simp only [W]; ring
  rw [hW]
  omega

/-- **The step of a branch, with the cost in the form of the clause `step_runs` of
`AsmBranchAt`.** This is `asmBrFull_step_runs` with one more hypothesis, the cap bound
`SparseCoreCapHyp` of the clause, and the cost `asmBrStepMul · (charge + (words + editWords + 1) ·
lg)`. The cost bound follows from `asmBrStep_cost_le`: the charge has the term `Enc(U_S) · lg`
(`branchStepCharge_ge`), the change record of P4 is at most `112 capExp² · charge` by the facts of
the model before the step (`lsfChangeSize_le_capExp_branchStepCharge`), and the limb count meets
the limb bound of the representation. -/
theorem asmBrFull_step_runs_clauseCost {HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
    {idx : ℕ → ℕ} (hsig : sig_outStepSmall_blocks_runs HasOutProcs idx) :
    ∃ mulOut : ℕ, ∀ {OS : OutTourSpec} {w : ℕ} {p : Program} {nm sm fm lm : ℕ}
      {TR : ℕ → ℕ → DSRep AsmTourAbs}
      {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
      {impl : SparsifyImpl} {depth P L capExp limbMul wordExp fCore : ℕ}
      {Ψ : BundleTreeState depth → ℕ}
      (J : AsmBrCoreStepAt TR B5 impl depth P L capExp limbMul wordExp w Ψ p fCore)
      {bOut bR fRoot readMul f : ℕ} {readIdx : ℕ → ℕ} {Q : RootQueryAt w p fRoot},
      (∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local) →
      (∀ vCap eCap, (TR vCap eCap).Local) → AsmBrOutProj OS TR w p nm sm fm lm →
      (∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH) →
      HasOutProcs p bOut nm sm fm lm →
      p.procs[f]? = some (asmBrStepStmt fCore (idx bOut) (bR + readIdx 2)) →
      let R := asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ
      ∀ (b cfH j batch words edits editWords fChgPtr outSlot reembSlot h fSplitPtr k M N vCap eCap n : ℕ)
        (tr : BundleTreeState depth) (ord : ℕ → List End) (x : R.τ) (U : List Update)
        (ed : List OrdEdit) (c : LSFChange) (SP : DSParams) (cap : ℕ) (mem : ℕ → ℕ) (pos : ℕ)
        (ω : ℕ → Bool),
      let ord' := applyOrdEdits ord ed
      let sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut :=
        fun _ => canonicalSparsify impl
      let info := stepBundleTree sparsify tr U ord ord'
      let chg := mem (fChgPtr + j)
      let spPtr := mem (fSplitPtr + j)
      ReadBranchAt (readRep vCap eCap x.tCap x.L_w P) w vCap eCap x.tCap x.L_w P SP cap p
        bR readIdx fRoot Q readMul →
      tr.m₀ = M → tr.n₀ = N → 1 ≤ depth → depth ≤ bundleLogFactor M N →
      depth ≤ Expander.chosenL ((M + N) ^ 2) →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      16 ≤ 2 ^ w →
      (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w →
      ((n + U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N →
      BranchUpdatesBelow impl tr n →
      BranchUpdatesBelow impl info.state (n + U.length) →
      R.rep b ⟨tr, ord, vCap, eCap⟩ x mem →
      AsmBrModelFacts impl vCap eCap tr ord →
      AsmBrModelFacts impl vCap eCap info.state ord' →
      SmallBatchAt mem batch tr.cs.G U words → tr.cs.G.BatchIsValid U →
      BatchWithinCaps vCap eCap U →
      OrdEditsAt mem edits ed editWords → OrderedBatch tr.cs.G U ord ord' →
      OrdEditsValidFor vCap eCap ord ed →
      OrdEditsForBatch tr.cs.G U ed →
      LSFChangeAt mem chg c → c.Exact tr.cs.lsf (compLSFBatch tr.cs U).lsf →
      SplitEntriesAt mem spPtr (canonSplitList tr.cs U) →
      InputAt w mem (R.foot b x) batch words h → InputAt w mem (R.foot b x) edits editWords h →
      InputAt w mem (R.foot b x) chg c.words h →
      InputAt w mem (R.foot b x) spPtr (splitEntriesWords (canonSplitList tr.cs U)) h →
      outSlot + 4 ≤ h → reembSlot + 2 ≤ h →
      (∀ a, outSlot ≤ a → a < outSlot + 4 → ¬ (reembSlot ≤ a ∧ a < reembSlot + 2)) →
      (∀ a, outSlot ≤ a → a < outSlot + 4 → ¬ R.foot b x a) →
      (∀ a, reembSlot ≤ a → a < reembSlot + 2 → ¬ R.foot b x a) →
      (∀ a, R.foot b x a → a < h) →
      (∀ a ∈ [b, cfH, j, batch, words, edits, editWords, fChgPtr, outSlot, reembSlot, h],
        a < 2 ^ w) →
      chg < 2 ^ w → fChgPtr + j < 2 ^ w → spPtr < 2 ^ w → fSplitPtr + j < 2 ^ w →
      (vCap + eCap + 2) ^ 2 < 2 ^ w →
      ZeroFrom mem h →
      h + asmBrStepSpace J.space readMul OS k M N L depth vCap eCap x.tCap x.L_w words editWords <
        2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' cst x',
        Runs w p ω body
          (startState [b, cfH, j, batch, words, edits, editWords, fChgPtr, outSlot, reembSlot, h,
            fSplitPtr] mem pos) o st' cst ∧
        R.rep b ⟨info.state, ord', vCap, eCap⟩ x' st'.mem ∧
        SmallBatchAt st'.mem (st'.mem outSlot) tr.S_cur info.U_S (st'.mem (outSlot + 1)) ∧
        h ≤ st'.mem outSlot ∧ st'.mem outSlot + st'.mem (outSlot + 1) ≤ o.value ∧
        (∃ outEd : List OrdEdit,
          OrdEditsAt st'.mem (st'.mem (outSlot + 2)) outEd (st'.mem (outSlot + 3)) ∧
          applyOrdEdits (tr.outOrder ord) outEd = info.state.outOrder ord' ∧
          OrdEditsValidFor vCap eCap (tr.outOrder ord) outEd ∧
          OrdEditsForBatch tr.S_cur info.U_S outEd) ∧
        h ≤ st'.mem (outSlot + 2) ∧ st'.mem (outSlot + 2) + st'.mem (outSlot + 3) ≤ o.value ∧
        readList st'.mem (st'.mem reembSlot) (st'.mem (reembSlot + 1)) =
          stepBundleTree_reembList sparsify tr U ord ord' ∧
        h ≤ st'.mem reembSlot ∧ st'.mem reembSlot + st'.mem (reembSlot + 1) ≤ o.value ∧
        h ≤ o.value ∧
        o.value ≤
          h + asmBrStepSpace J.space readMul OS k M N L depth vCap eCap x.tCap x.L_w words editWords ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ R.foot b x a → ¬ (outSlot ≤ a ∧ a < outSlot + 4) →
          ¬ (reembSlot ≤ a ∧ a < reembSlot + 2) → st'.mem a = mem a) ∧
        (∀ a, R.foot b x' a → R.foot b x a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ t < st'.mem (outSlot + 3), st'.mem (st'.mem (outSlot + 2) + t) < 2 ^ w) ∧
        (∀ a, st'.mem outSlot ≤ a → a < st'.mem outSlot + st'.mem (outSlot + 1) → ¬ R.foot b x' a) ∧
        (∀ a, st'.mem (outSlot + 2) ≤ a → a < st'.mem (outSlot + 2) + st'.mem (outSlot + 3) →
          ¬ R.foot b x' a) ∧
        st'.mem (outSlot + 3) ≤
          asmBrEdMul J.ysMul * (branchStepCharge sparsify tr U ord ord' +
            (words + editWords + 1) * bundleLogFactor M N) ∧
        cst + R.phi b x' st'.mem ≤
          asmBrStepMul J.mul J.ysMul mulOut OS.mul readMul capExp limbMul *
              (branchStepCharge sparsify tr U ord ord' +
                (words + editWords + 1) * bundleLogFactor M N) +
            R.phi b x mem := by
  obtain ⟨mulOut, hrun⟩ := asmBrFull_step_runs hsig
  refine ⟨mulOut, ?_⟩
  intro OS w p nm sm fm lm TR B5 impl depth P L capExp limbMul wordExp fCore Ψ J bOut bR fRoot
    readMul f readIdx Q hB5 hTR hOP hTh hHas hf R b cfH j batch words edits editWords fChgPtr
    outSlot reembSlot h fSplitPtr k M N vCap eCap n tr ord x U ed c SP cap mem pos ω ord' sparsify
    info chg spPtr hB hM hN hdepth hdepth_lg hdepth_ch hcapH h16 hword hThU hBUn hBUn' hrep hold hnew hBat hBU hcaps hEd hord
    hEdV hEdB hC hc hSpAt hBin hEin hCin hSpin hos hrs hslots hosF hrsF hfoot hargs hchgW hchgjW
    hspW hspjW hw2 hz hspace
  obtain ⟨body, hbody, o, st', cst, x', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16', hEdLt, hDisjB, hDisjE, hEdW, hcost⟩ := hrun J hB5 hTR hOP hTh hHas hf b cfH j batch words edits editWords fChgPtr
      outSlot reembSlot h fSplitPtr k M N vCap eCap n tr ord x U ed c SP cap mem pos ω hB hM hN
      hdepth hdepth_lg hdepth_ch h16 hword hThU hBUn hBUn' hrep hold hnew hBat hBU hcaps hEd hord hEdV hEdB hC hc hSpAt hBin
      hEin hCin hSpin hos hrs hslots hosF hrsF hfoot hargs hchgW hchgjW hspW hspjW hw2 hz hspace
  have hEnc := branchStepCharge_ge sparsify tr U ord ord'
  rw [hM, hN] at hEnc
  refine ⟨body, hbody, o, st', cst, x', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16', hEdLt, hDisjB, hDisjE, asmBrStep_eW_le hEdW hEnc,
    le_trans hcost (Nat.add_le_add_right ?_ _)⟩
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLwB, -⟩, -⟩ :=
    hrep
  have hLw : x.L_w ≤
      L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) := by
    rw [← hM, ← hN]; exact hLwB
  have hcap' : vCap + eCap + 2 ≤ (tr.m₀ + tr.n₀ + 2) ^ capExp := by rw [hM, hN]; exact hcapH.1
  have hcs := lsfChangeSize_le_capExp_branchStepCharge sparsify hold hBU hcap' (ord' := ord')
  exact asmBrStep_cost_le hEnc hcs (le_trans (by omega) hcapH.1) hcapH.2 hLw

end MinCostFlow.SparseCore.Program
