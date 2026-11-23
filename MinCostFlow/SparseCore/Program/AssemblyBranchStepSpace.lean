module

public import MinCostFlow.SparseCore.Program.AssemblyBranchStepCost

/-!
# The space of the step of a branch as a polynomial (`AssemblyBranchStepSpace`)

The clause `step_runs` of `AsmBranchAt` bounds the new cells of the step by a polynomial
`S.stepSpace capExp` at `x = M + N + k + vCap + eCap + L + depth + words + editWords`. The step of
a branch (`asmBrFull_step_runs_clauseCost`, `AssemblyBranchStepCost.lean`) allocates at most
`asmBrStepSpace J.space readMul OS vCap eCap tCap L_w words editWords` cells
(`AssemblyBranchStepFrame.lean`). That is the space of the first phase, P7's output step and
P10's update. This file bounds it by the polynomial `asmBrStepPoly` (`asmBrStepSpace_le_poly`)
and restates the step with it (`asmBrFull_step_runs_clause`). The first phase has its space
below the polynomial `J.spaceP` of its interface `AsmBrCoreStepAt`.

**The route.** Write `B = x + 2`. Every input size is at most `B`. The representation of the
branch gives `tCap ≤ 2 (vCap + eCap + 2) ^ 2 ≤ 2 B ²` and the limb bound
`L_w ≤ L + (capExp + 128) (log₂ (M + N + 2) + 1)`, so `L_w + 1 ≤ (capExp + 129) B`. Then:
* the first phase allocates at most `JP.eval (X + …)` cells, for a polynomial `JP` that bounds its
  space, at an argument below `2 B`, so at most `JP.coeff · 2 ^ JP.deg · B ^ JP.deg` cells;
* P7's output step allocates at most `1000 (vCap + 1) (eCap + 1) (q + 1) ≤ 1000 (q + 1) B ²` cells,
  with `q` the query space of the tour;
* P10's update allocates at most `readMul (vCap + tCap + X + 1) (L_w + 1)` cells, where `X` is the
  number of words it reads, at most `(1000 q + 1004) B ²` with the terms before, so at most
  `readMul (1000 q + 1004) (capExp + 129) B ³` cells.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Read

/-- **The space of the step of a branch**: a polynomial of degree `JP.deg + 3`, from the
polynomial `JP` that bounds the space of the first phase, P10's multiplier `readMul`, the query
space `qSpace` of the tour and `capExp`. -/
def asmBrStepPoly (JP : PolyBound) (readMul qSpace capExp : ℕ) : PolyBound where
  coeff := JP.coeff * 2 ^ JP.deg + 1000 * (qSpace + 1) +
    readMul * (1000 * qSpace + 1004) * (capExp + 129)
  deg := JP.deg + 3

/-- **The space of the step is at most `asmBrStepPoly`**, from a polynomial bound `JP` on the space
of the first phase, the bound on `tCap` and the limb bound of the representation. -/
theorem asmBrStepSpace_le_poly {JP : PolyBound} {space : ℕ → ℕ} (hJ : ∀ x, space x ≤ JP.eval x)
    (readMul : ℕ) (OS : OutTourSpec)
    {k M N L depth vCap eCap tCap L_w words editWords capExp : ℕ}
    (htc : tCap ≤ 2 * (vCap + eCap + 2) ^ 2)
    (hLw : L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)) :
    asmBrStepSpace space readMul OS k M N L depth vCap eCap tCap L_w words editWords ≤
      (asmBrStepPoly JP readMul OS.querySpace capExp).eval
        (M + N + k + vCap + eCap + L + depth + words + editWords) := by
  set B := M + N + k + vCap + eCap + L + depth + words + editWords + 2 with hBdef
  set d := JP.deg
  have hB : 2 ≤ B := by omega
  have hBpos : 0 < B := by omega
  have hpw : ∀ {a b : ℕ}, a ≤ b → B ^ a ≤ B ^ b := fun h => Nat.pow_le_pow_right hBpos h
  have hB2 : B ≤ B ^ 2 := Nat.le_self_pow (by norm_num) B
  have hval : (asmBrStepPoly JP readMul OS.querySpace capExp).eval
      (M + N + k + vCap + eCap + L + depth + words + editWords) =
      (JP.coeff * 2 ^ d + 1000 * (OS.querySpace + 1) +
        readMul * (1000 * OS.querySpace + 1004) * (capExp + 129)) * B ^ (d + 3) := rfl
  rw [hval]
  unfold asmBrStepSpace
  -- the first phase
  have hT1 : space (M + N + k + vCap + eCap + L + depth + words + editWords) ≤
      JP.coeff * 2 ^ d * B ^ (d + 3) := by
    refine (hJ _).trans ?_
    have h1 : M + N + k + vCap + eCap + L + depth + words + editWords + 2 ≤ 2 * B := by omega
    calc JP.coeff * (M + N + k + vCap + eCap + L + depth + words + editWords + 2) ^ d
        ≤ JP.coeff * (2 * B) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
      _ = JP.coeff * 2 ^ d * B ^ d := by rw [mul_pow, ← Nat.mul_assoc]
      _ ≤ JP.coeff * 2 ^ d * B ^ (d + 3) := Nat.mul_le_mul_left _ (hpw (by omega))
  -- P7's output step
  have hO : outStepSpace OS vCap eCap ≤ 1000 * (OS.querySpace + 1) * B ^ 2 := by
    unfold outStepSpace
    calc 1000 * (vCap + 1) * (eCap + 1) * (OS.querySpace + 1)
        ≤ 1000 * B * B * (OS.querySpace + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega))
      _ = 1000 * (OS.querySpace + 1) * B ^ 2 := by ring
  have hT2 : outStepSpace OS vCap eCap ≤ 1000 * (OS.querySpace + 1) * B ^ (d + 3) :=
    hO.trans (Nat.mul_le_mul_left _ (hpw (by omega)))
  -- P10's update
  have htB : tCap ≤ 2 * B ^ 2 :=
    htc.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 2))
  have hlog : Nat.log 2 (M + N + 2) + 1 ≤ B := by
    have := Nat.log_lt_self 2 (show M + N + 2 ≠ 0 by omega); omega
  have hLw1 : L_w + 1 ≤ (capExp + 129) * B := by
    have h1 : (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ≤
        (capExp + 128) * B := Nat.mul_le_mul_left _ hlog
    have e : (capExp + 129) * B = (capExp + 128) * B + B := by ring
    have : sparseCoreReadout2LimbConst = 128 := rfl
    omega
  have hX : vCap + tCap + (words + (vCap + eCap + 2) + outStepSpace OS vCap eCap) + 1 ≤
      (1000 * OS.querySpace + 1004) * B ^ 2 := by
    have e : (1000 * OS.querySpace + 1004) * B ^ 2 =
        1000 * (OS.querySpace + 1) * B ^ 2 + 2 * B ^ 2 + 2 * B ^ 2 := by ring
    omega
  have hT3 : readSpace readMul vCap tCap L_w
      (words + (vCap + eCap + 2) + outStepSpace OS vCap eCap) ≤
      readMul * (1000 * OS.querySpace + 1004) * (capExp + 129) * B ^ (d + 3) := by
    unfold readSpace
    calc readMul * (vCap + tCap + (words + (vCap + eCap + 2) + outStepSpace OS vCap eCap) + 1) *
          (L_w + 1)
        ≤ readMul * ((1000 * OS.querySpace + 1004) * B ^ 2) * ((capExp + 129) * B) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hX) hLw1
      _ = readMul * (1000 * OS.querySpace + 1004) * (capExp + 129) * B ^ 3 := by ring
      _ ≤ readMul * (1000 * OS.querySpace + 1004) * (capExp + 129) * B ^ (d + 3) :=
          Nat.mul_le_mul_left _ (hpw (by omega))
  have e : (JP.coeff * 2 ^ d + 1000 * (OS.querySpace + 1) +
      readMul * (1000 * OS.querySpace + 1004) * (capExp + 129)) * B ^ (d + 3) =
      JP.coeff * 2 ^ d * B ^ (d + 3) + 1000 * (OS.querySpace + 1) * B ^ (d + 3) +
        readMul * (1000 * OS.querySpace + 1004) * (capExp + 129) * B ^ (d + 3) := by ring
  omega

/-- **The step of a branch in the form of the clause `step_runs` of `AsmBranchAt`**, with the
cost of `asmBrFull_step_runs_clauseCost` and the space `asmBrStepPoly` at
`M + N + k + vCap + eCap + L + depth + words + editWords`, with `J.spaceP` for the space of the
first phase. The bound on `tCap` and the limb bound come from the representation. -/
theorem asmBrFull_step_runs_clause {HasOutProcs : Program → ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
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
      let sp := asmBrStepPoly J.spaceP readMul OS.querySpace capExp
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
      h + sp.eval (M + N + k + vCap + eCap + L + depth + words + editWords) < 2 ^ w →
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
        o.value ≤ h + sp.eval (M + N + k + vCap + eCap + L + depth + words + editWords) ∧
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
  obtain ⟨mulOut, hrun⟩ := asmBrFull_step_runs_clauseCost hsig
  refine ⟨mulOut, ?_⟩
  intro OS w p nm sm fm lm TR B5 impl depth P L capExp limbMul wordExp fCore Ψ J bOut bR fRoot
    readMul f readIdx Q hB5 hTR hOP hTh hHas hf R sp b cfH j batch words edits editWords fChgPtr
    outSlot reembSlot h fSplitPtr k M N vCap eCap n tr ord x U ed c SP cap mem pos ω ord' sparsify
    info chg spPtr hB hM hN hdepth hdepth_lg hdepth_ch hcapH h16 hword hThU hBUn hBUn' hrep hold hnew hBat hBU hcaps hEd hord
    hEdV hEdB hC hc hSpAt hBin hEin hCin hSpin hos hrs hslots hosF hrsF hfoot hargs hchgW hchgjW
    hspW hspjW hw2 hz hspace
  have hsp : asmBrStepSpace J.space readMul OS k M N L depth vCap eCap x.tCap x.L_w words editWords ≤
      sp.eval (M + N + k + vCap + eCap + L + depth + words + editWords) := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLwB, -⟩, -, -,
      hvc, hec, htc, -⟩ := hrep
    have hLw : x.L_w ≤
        L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) := by
      rw [← hM, ← hN]; exact hLwB
    have htc' : x.tCap ≤ 2 * (vCap + eCap + 2) ^ 2 := by
      have hv : x.vCap = vCap := hvc
      have he : x.eCap = eCap := hec
      rw [← hv, ← he]; exact htc
    exact asmBrStepSpace_le_poly J.space_le readMul OS htc' hLw
  obtain ⟨body, hbody, o, st', cst, x', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16', hEdLt, hDisjB, hDisjE, hEdW, hcost⟩ := hrun J hB5 hTR hOP hTh hHas hf b cfH j batch words edits editWords fChgPtr
      outSlot reembSlot h fSplitPtr k M N vCap eCap n tr ord x U ed c SP cap mem pos ω hB hM hN
      hdepth hdepth_lg hdepth_ch hcapH h16 hword hThU hBUn hBUn' hrep hold hnew hBat hBU hcaps hEd hord hEdV hEdB hC hc hSpAt
      hBin hEin hCin hSpin hos hrs hslots hosF hrsF hfoot hargs hchgW hchgjW hspW hspjW hw2 hz
      (lt_of_le_of_lt (Nat.add_le_add_left hsp h) hspace)
  exact ⟨body, hbody, o, st', cst, x', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13.trans (Nat.add_le_add_left hsp h), h14, h15, h16', hEdLt, hDisjB, hDisjE, hEdW, hcost⟩

end MinCostFlow.SparseCore.Program
