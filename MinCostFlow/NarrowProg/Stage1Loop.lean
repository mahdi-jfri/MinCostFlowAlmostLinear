module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.BitScale
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1Layout
public import MinCostFlow.NarrowProg.Stage1Start
public import MinCostFlow.NarrowProg.Stage1Round
import MinCostFlow.Narrow.CostUnitsClip
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Top-level Stage 1 cost-scaling loop (`stage1Circ`, Part 6)

Implements `stage1Circ (startIdx roundIdx) (pIn, pOut, h)`:
- If `m = 0`, writes `[h, 2]` to `pOut` and returns `h` immediately (vacuously optimal).
- Otherwise calls `stage1Start(pIn, h)`, runs `narrowCostRounds C` iterations of
  `stage1Round(h, j, curH)` maintaining `RoundInvariantState`, writes `[lay.pFlow, K_cap]`
  to `pOut`, discards working buffers into `Assn.gc`, and returns the final heap pointer.

Proves `stage1Circ_meets` with explicit cost `stage1CircCost` and `stage1Circ_meetsO`
in the `outer_work_compressed_bound` shape.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate List.length_append List.length_map

/-! ### Helper lemmas for `stage1Circ` -/

private theorem optimal_zero_of_m_eq_zero (I : Circulation) (hm0 : I.m = 0) :
    I.Optimal (fun _ : Fin I.m => ((0 : ℤ) : ℝ)) := by
  have hempty : ∀ e : Fin I.m, False := fun e => by have := e.isLt; omega
  have hfeas : I.Feasible (fun _ : Fin I.m => ((0 : ℤ) : ℝ)) := by
    refine ⟨fun v => ?_, fun e => (hempty e).elim⟩
    unfold Circulation.balance
    simp [Finset.sum_eq_zero fun e _ => (hempty e).elim]
  refine ⟨hfeas, fun g _ => ?_⟩
  unfold Circulation.objective
  rw [Finset.sum_eq_zero fun e _ => (hempty e).elim,
      Finset.sum_eq_zero fun e _ => (hempty e).elim]

private theorem two_mul_le_two_pow : ∀ k : ℕ, 2 * k ≤ 2 ^ k
  | 0 => by decide
  | 1 => by decide
  | k + 1 => by
    have ih := two_mul_le_two_pow k
    have hpow : 1 ≤ 2 ^ k := Nat.two_pow_pos k
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    rcases k with _ | k'
    · decide
    · have h2le : 2 ≤ 2 ^ (k' + 1) := by
        have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ k' + 1)
        simpa using this
      omega

private theorem K_cap_mul_k_lt {w k : ℕ} {I : Circulation} {S : ℕ → ℕ → ℕ}
    (hm : 0 < I.m) (hk : 1 ≤ k) (h2k : 2 * k ≤ w) (h2mk : 2 * I.m + 1 < 2 ^ k)
    (hsp : stage1CircSpace I k S < 2 ^ w) :
    (bitScalingPhases I / k + 2) * k < 2 ^ w := by
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk1 : k = 1 := by omega
    rw [hk1] at h2mk; omega
  have h4_le : 4 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk2
    simpa using this
  have h2k_le : 2 * k ≤ 2 ^ k := two_mul_le_two_pow k
  have hpow_w : 2 ^ k * 2 ^ k ≤ 2 ^ w := by
    rw [← pow_add, show k + k = 2 * k by omega]
    exact Nat.pow_le_pow_right (by decide) h2k
  have h8k : 4 * (2 * k) ≤ 2 ^ w :=
    le_trans (Nat.mul_le_mul h4_le h2k_le) hpow_w
  have hnr1 : 1 ≤ narrowCostRounds I.compress := by
    unfold narrowCostRounds; omega
  have hTU_le : 26 * bitScalingPhases I ≤ stage1CircSpace I k S := by
    have hsp0 : stage1CircSpace I k S =
        stage1StartSpace I k + narrowCostRounds I.compress *
          (stage1RoundBitScaleSpace I.compress k S + stage1DualSpace I.compress S) := by
      unfold stage1CircSpace; simp [hm.ne']
    have h1 : 26 * bitScalingPhases I ≤ stage1RoundBitScaleSpace I.compress k S := by
      have h26 : 26 ≤ 2 + 24 * I.compress.m + S (I.compress.n + 1) (4 * I.compress.m) := by
        change 26 ≤ 2 + 24 * I.m + _; omega
      have hmul := Nat.mul_le_mul_left (bitScalingPhases I.compress) h26
      have hT_eq : bitScalingPhases I.compress = bitScalingPhases I := rfl
      rw [Nat.mul_comm] at hmul
      unfold stage1RoundBitScaleSpace
      rw [← hT_eq]
      omega
    have h2 : stage1RoundBitScaleSpace I.compress k S ≤
        narrowCostRounds I.compress *
          (stage1RoundBitScaleSpace I.compress k S + stage1DualSpace I.compress S) := by
      calc stage1RoundBitScaleSpace I.compress k S
          ≤ 1 * (stage1RoundBitScaleSpace I.compress k S + stage1DualSpace I.compress S) := by omega
        _ ≤ _ := Nat.mul_le_mul_right _ hnr1
    have h3 := le_trans h1 h2
    omega
  have hdiv_le : bitScalingPhases I / k * k ≤ bitScalingPhases I :=
    Nat.div_mul_le_self (bitScalingPhases I) k
  rw [Nat.add_mul]
  omega

private theorem narrowCostRounds_lt_of_space {w k : ℕ} {I : Circulation} {S : ℕ → ℕ → ℕ}
    (hm : 0 < I.m) (hsp : stage1CircSpace I k S < 2 ^ w) :
    narrowCostRounds I.compress < 2 ^ w := by
  have h5 : 5 ≤ stage1RoundBitScaleSpace I.compress k S := by
    unfold stage1RoundBitScaleSpace; omega
  have hsp0 : stage1CircSpace I k S =
      stage1StartSpace I k + narrowCostRounds I.compress *
        (stage1RoundBitScaleSpace I.compress k S + stage1DualSpace I.compress S) := by
    unfold stage1CircSpace; simp [hm.ne']
  have h1 : narrowCostRounds I.compress ≤
      narrowCostRounds I.compress *
        (stage1RoundBitScaleSpace I.compress k S + stage1DualSpace I.compress S) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (narrowCostRounds I.compress) (by omega : 1 ≤ _)
  omega

private def s1InNoDesc (I : Circulation) (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) : Assn :=
  Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val) *
  Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val) *
  Assn.list pCapPtrs capPtrs *
  Assn.list pCapLens (capLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
  Assn.list pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
  Assn.list pCostPtrs costPtrs *
  Assn.list pCostLens (costLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j []))

private theorem s1In_split_desc (I : Circulation) (k : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) :
    stage1Input I k capPtrs capLimbs costPtrs costLimbs
      pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens =
    Assn.list pIn [I.n, I.m, k, pTail, pHead, pCapPtrs, pCapLens, pCostSign, pCostPtrs, pCostLens] *
    s1InNoDesc I capPtrs capLimbs costPtrs costLimbs
      pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens := by
  unfold stage1Input s1InNoDesc
  simp only [mul_assoc]

private def s1InLoopFrame (I : Circulation) (k : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) : Assn :=
  Assn.list pIn [I.n, I.m, k, pTail, pHead, pCapPtrs, pCapLens, pCostSign, pCostPtrs, pCostLens] *
  Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val) *
  Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val) *
  Assn.list pCapPtrs capPtrs *
  Assn.list pCapLens (capLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
  Assn.list pCostPtrs costPtrs *
  (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j []))

private lemma perm10_loop {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Assn} :
    a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 =
      (a1 * a2 * a3 * a4 * a5 * a6 * a8 * a10) * a7 * a9 := by
  simp only [mul_left_comm, mul_comm]

private theorem s1In_split_loop (I : Circulation) (k : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) :
    stage1Input I k capPtrs capLimbs costPtrs costLimbs
      pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens =
    s1InLoopFrame I k capPtrs capLimbs costPtrs costLimbs
      pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens *
    Assn.list pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
    Assn.list pCostLens (costLimbs.map List.length) := by
  unfold stage1Input s1InLoopFrame
  exact perm10_loop

private def s1WorkNoCtx (I : Circulation) (k : ℕ) (lay : Stage1Layout)
    (capLimbs costLimbs : List (List ℕ)) (adjPtrs : List ℕ) (adjLimbs : List (List ℕ))
    (s : NarrowCostState I.compress) (flowLimbs : Fin I.m → List ℕ)
    (resCSign resCMag resCapLens resOut : List ℕ)
    (resFwdLimbs : Fin I.m → List ℕ) (tmp1 tmp2 : List ℕ) : Assn :=
  let K_cap := bitScalingPhases I / k + 2
  let fwdPtrs := List.ofFn fun e : Fin I.m => lay.pResFwdBuf + e.val * K_cap
  let revPtrs := List.ofFn fun e : Fin I.m => lay.pFlow + e.val * K_cap
  Assn.list lay.pResIn
    [I.compress.n, 2 * I.m, k, lay.pResTail, lay.pResHead, lay.pResCSign, lay.pResCMag,
     lay.pResCapPtrs, lay.pResCapLens] *
  Assn.list lay.pResOut resOut *
  s1CompFixed I lay adjPtrs adjLimbs *
  s1SmallState I lay s *
  s1ResEp I lay *
  Assn.list lay.pResCSign resCSign *
  Assn.list lay.pResCMag resCMag *
  Assn.list lay.pResCapPtrs (fwdPtrs ++ revPtrs) *
  Assn.list lay.pResCapLens resCapLens *
  (∏ j ∈ Finset.range I.m, Assn.list (lay.pCapBuf + j * K_cap) (padLimbs K_cap (capLimbs.getD j []))) *
  (∏ j ∈ Finset.range I.m, Assn.list (lay.pFlow + j * K_cap) (if h : j < I.m then flowLimbs ⟨j, h⟩ else [])) *
  (∏ j ∈ Finset.range I.m, Assn.list (lay.pResFwdBuf + j * K_cap) (if h : j < I.m then resFwdLimbs ⟨j, h⟩ else [])) *
  s1Tmps lay tmp1 tmp2 *
  ⌜costLimbs.length = I.m ∧ adjPtrs.length = I.m ∧ adjLimbs.length = I.m ∧
    resCSign.length = 2 * I.m ∧ resCMag.length = 2 * I.m ∧ resCapLens.length = 2 * I.m ∧
    resOut.length = 4 ∧ tmp1.length = K_cap ∧ tmp2.length = K_cap ∧
    (∀ e : Fin I.m, (resFwdLimbs e).length = K_cap)⌝

private theorem s1Work_split_ctx (I : Circulation) (k : ℕ) (lay : Stage1Layout)
    (pCostSign pCostLens : ℕ) (capLimbs costLimbs : List (List ℕ))
    (adjPtrs : List ℕ) (adjLimbs : List (List ℕ))
    (s : NarrowCostState I.compress) (flowLimbs : Fin I.m → List ℕ)
    (resCSign resCMag resCapLens resOut : List ℕ)
    (resFwdLimbs : Fin I.m → List ℕ) (tmp1 tmp2 : List ℕ) :
    stage1WorkingAssn I k lay pCostSign pCostLens capLimbs costLimbs adjPtrs adjLimbs
      s flowLimbs resCSign resCMag resCapLens resOut resFwdLimbs tmp1 tmp2 =
    Assn.list lay.pCtx
      [I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I,
       bitScalingPhases I / k + 2, lowerClip I.m, upperClip I.m] *
    Assn.list (lay.pCtx + 8)
      [freezeThreshold I.m, narrowCostRounds I.compress, lay.pCompTail, lay.pCompHead,
       pCostSign, pCostLens, lay.pAdjCostPtrs, lay.pCapBuf] *
    Assn.list (lay.pCtx + 16)
      [lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
       lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn] *
    s1WorkNoCtx I k lay capLimbs costLimbs adjPtrs adjLimbs
      s flowLimbs resCSign resCMag resCapLens resOut resFwdLimbs tmp1 tmp2 := by
  rw [stage1Working_unfold, s1CtxHdr_split]
  unfold s1WorkNoCtx
  simp only [mul_assoc]

private lemma extract_exit_perm
    {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 : Assn} :
    a1 * (a2 * (a3 * (a4 * (a5 * (a6 * (a7 * (a8 * (a9 * (a10 * (a11 * (a12 * (a13 *
      (a14 * (a15 * (a16 * a17))))))))))))))) =
    a1 * a3 * a14 *
      (a2 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a15 * a16 * a17) := by
  simp only [mul_left_comm, mul_comm]

private theorem stage1Working_extract_exit (I : Circulation) (k : ℕ) (lay : Stage1Layout)
    (pCostSign pCostLens : ℕ) (capLimbs costLimbs : List (List ℕ))
    (adjPtrs : List ℕ) (adjLimbs : List (List ℕ))
    (s : NarrowCostState I.compress) (flowLimbs : Fin I.m → List ℕ)
    (resCSign resCMag resCapLens resOut : List ℕ)
    (resFwdLimbs : Fin I.m → List ℕ) (tmp1 tmp2 : List ℕ) :
    let K_cap := bitScalingPhases I / k + 2
    stage1WorkingAssn I k lay pCostSign pCostLens capLimbs costLimbs adjPtrs adjLimbs
      s flowLimbs resCSign resCMag resCapLens resOut resFwdLimbs tmp1 tmp2 ≤
    Assn.list lay.pCtx
      [I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I,
       bitScalingPhases I / k + 2, lowerClip I.m, upperClip I.m] *
    Assn.list (lay.pCtx + 16)
      [lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
       lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn] *
    (∏ j ∈ Finset.range I.m, Assn.list (lay.pFlow + j * K_cap)
      (if h : j < I.m then flowLimbs ⟨j, h⟩ else [])) * Assn.gc := by
  rw [s1Work_split_ctx]
  unfold s1WorkNoCtx
  dsimp only
  conv_lhs => simp only [mul_assoc]; rw [extract_exit_perm]
  refine Assn.mul_le_mul_of_le le_rfl ?_
  have hnd : ∀ (A B : Assn), A.NoDebt → B.NoDebt → (A * B).NoDebt := fun _ _ hA hB => hA.mul hB
  have hcf : (s1CompFixed I lay adjPtrs adjLimbs).NoDebt := by
    unfold s1CompFixed
    exact hnd _ _ (hnd _ _ (hnd _ _ (Assn.noDebt_list _ _) (Assn.noDebt_list _ _))
      (Assn.noDebt_list _ _)) (Assn.noDebt_prod _ fun _ _ => Assn.noDebt_list _ _)
  have hss : (s1SmallState I lay s).NoDebt := by
    unfold s1SmallState
    exact hnd _ _ (hnd _ _ (Assn.noDebt_list _ _) (Assn.noDebt_list _ _)) (Assn.noDebt_list _ _)
  have hre : (s1ResEp I lay).NoDebt := by
    unfold s1ResEp
    exact hnd _ _ (Assn.noDebt_list _ _) (Assn.noDebt_list _ _)
  have htm : (s1Tmps lay tmp1 tmp2).NoDebt := by
    unfold s1Tmps
    exact hnd _ _ (Assn.noDebt_list _ _) (Assn.noDebt_list _ _)
  exact hnd _ _ (hnd _ _ (hnd _ _ (hnd _ _ (hnd _ _ (hnd _ _ (hnd _ _ (hnd _ _ (hnd _ _
    (hnd _ _ (hnd _ _ (hnd _ _ (hnd _ _
      (Assn.noDebt_list _ _) (Assn.noDebt_list _ _)) (Assn.noDebt_list _ _))
      hcf) hss) hre) (Assn.noDebt_list _ _)) (Assn.noDebt_list _ _))
      (Assn.noDebt_list _ _)) (Assn.noDebt_list _ _))
      (Assn.noDebt_prod _ fun _ _ => Assn.noDebt_list _ _))
      (Assn.noDebt_prod _ fun _ _ => Assn.noDebt_list _ _))
      htm) (Assn.noDebt_pure _)

/-! ### Top-level `stage1Circ` procedure and specification -/

/-- Top-level Stage 1 circulation solver: handles `m = 0` directly, otherwise initializes
with `stage1Start`, runs `narrowCostRounds C` calls to `stage1Round`, writes `[pFlow, K_cap]`
to `pOut`, and returns the final heap pointer. -/
wram_def stage1Circ (startIdx roundIdx : ℕ) (pIn, pOut, h) {
  m := mem[pIn + 1]
  if m == 0 {
    mem[pOut] := h
    mem[pOut + 1] := 2
    return h
  } else {
    curH := startIdx(pIn, h)
    numRounds := mem[h + 9]
    j := 0
    while j < numRounds {
      curH := roundIdx(h, j, curH)
      j := j + 1
    }
    pFlow := mem[h + 16]
    Kcap := mem[h + 5]
    mem[pOut] := pFlow
    mem[pOut + 1] := Kcap
    return curH
  }
}

/-- Explicit work bound of `stage1Circ`. -/
def stage1CircCost (T_bs_max : ℕ → ℕ → ℕ → ℕ → ℕ) (T_sol : ℕ → ℕ → ℕ) (Tcb : ℕ)
    (I : Circulation) (k : ℕ) : ℕ :=
  if I.m = 0 then 60
  else
    let C := I.compress
    stage1StartCost I k +
      narrowCostRounds C * (stage1RoundCost T_bs_max T_sol Tcb I k + 25) + 250

/-- Ghost loop-state bundle for `sep_while` inside `stage1Circ`. -/
private structure Stage1LoopGhost (I : Circulation) where
  j : ℕ
  curH : ℕ
  s : NarrowCostState I.compress
  y : Fin I.compress.n → ℤ
  flowLimbs : Fin I.m → List ℕ
  resCSign : List ℕ
  resCMag : List ℕ
  resCapLens : List ℕ
  resOut : List ℕ
  resFwdLimbs : Fin I.m → List ℕ
  tmp1 : List ℕ
  tmp2 : List ℕ

private theorem stage1Circ_exit {w : ℕ} {p : Program} {S : ℕ → ℕ → ℕ}
    (I : Circulation) (k : ℕ) (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pIn pOut h pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens ob0 ob1 R : ℕ)
    (t : Stage1LoopGhost I) (c : ℤ)
    (lay : Stage1Layout) (hlay_ctx : lay.pCtx = h)
    (adjPtrs : List ℕ) (adjLimbs : List (List ℕ))
    (hh_le : h ≤ t.curH) (hcurH_le : t.curH ≤ h + stage1CircSpace I k S)
    (hoptI : I.Optimal (fun e => (t.s.flow e : ℝ)))
    (hfl : ∀ e : Fin I.m, 0 ≤ t.s.flow e ∧ Limbs k (t.flowLimbs e) ∧
      (t.flowLimbs e).length = bitScalingPhases I / k + 2 ∧
      ((Nat.ofDigits (2 ^ k) (t.flowLimbs e) : ℕ) : ℤ) = t.s.flow e)
    (hc : (30 : ℤ) ≤ c) :
    SE w p stage1Circ.vars
      [pIn, pOut, h, I.m, t.curH, R, t.j, 0, 0] c
      [Assn.list pOut [ob0, ob1],
       s1InLoopFrame I k capPtrs capLimbs costPtrs costLimbs
         pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens,
       stage1WorkingAssn I k lay pCostSign pCostLens capLimbs costLimbs adjPtrs adjLimbs
         t.s t.flowLimbs t.resCSign t.resCMag t.resCapLens t.resOut t.resFwdLimbs t.tmp1 t.tmp2,
       Assn.list pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0),
       Assn.list pCostLens (costLimbs.map List.length),
       Assn.free t.curH (2 ^ w - t.curH)]
      (Stmt.assign 7 (Expr.load (Expr.bin .add (Expr.reg 2) (Expr.const 16))) ;;
       Stmt.assign 8 (Expr.load (Expr.bin .add (Expr.reg 2) (Expr.const 5))) ;;
       Stmt.store (Expr.reg 1) (Expr.reg 7) ;;
       Stmt.store (Expr.bin .add (Expr.reg 1) (Expr.const 1)) (Expr.reg 8) ;;
       Stmt.ret (Expr.reg 4))
      (fun o _ => (stage1CircSpec w S).post
        (I, k, capPtrs, capLimbs, costPtrs, costLimbs, [ob0, ob1]) [pIn, pOut, h] o.value) := by
  set K_cap := bitScalingPhases I / k + 2
  sep_apply (s1In_split_loop I k capPtrs capLimbs costPtrs costLimbs
    pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens).symm
  have hexit := stage1Working_extract_exit I k lay pCostSign pCostLens capLimbs costLimbs
    adjPtrs adjLimbs t.s t.flowLimbs t.resCSign t.resCMag t.resCapLens t.resOut t.resFwdLimbs
    t.tmp1 t.tmp2
  rw [hlay_ctx] at hexit
  sep_apply hexit
  iterate 2 sep_step
  subst pFlow Kcap
  dsimp only [List.getElem_cons_succ, List.getElem_cons_zero]
  have hdrop0 : Assn.list h
      [I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I,
       bitScalingPhases I / k + 2, lowerClip I.m, upperClip I.m] ≤ Assn.gc :=
    Assn.noDebt_list _ _
  have hdrop16 : Assn.list (h + 16)
      [lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
       lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn] ≤ Assn.gc :=
    Assn.noDebt_list _ _
  sep_apply hdrop0
  sep_apply hdrop16
  iterate 2 sep_step
  dsimp only [List.set]
  sep_step
  refine le_trans ?_ (Assn.mul_le_mul_of_le
    (le_iSup_of_le pIn <| le_iSup_of_le pOut <| le_iSup_of_le h <| le_iSup_of_le pTail <|
      le_iSup_of_le pHead <| le_iSup_of_le pCapPtrs <| le_iSup_of_le pCapLens <|
      le_iSup_of_le pCostSign <| le_iSup_of_le pCostPtrs <| le_iSup_of_le pCostLens <|
      le_iSup_of_le lay.pFlow <| le_iSup_of_le t.s.flow <| le_iSup_of_le t.flowLimbs le_rfl) le_rfl)
  have hpure_out : [pIn, pOut, h] = [pIn, pOut, h] ∧ h ≤ t.curH ∧
      t.curH ≤ h + stage1CircSpace I k S ∧ I.Optimal (fun e => (t.s.flow e : ℝ)) ∧
      ∀ e : Fin I.m, 0 ≤ t.s.flow e ∧ Limbs k (t.flowLimbs e) ∧
        (t.flowLimbs e).length = K_cap ∧
        ((Nat.ofDigits (2 ^ k) (t.flowLimbs e) : ℕ) : ℤ) = t.s.flow e :=
    ⟨rfl, hh_le, hcurH_le, hoptI, hfl⟩
  rw [eq_true hpure_out, Assn.pure_true, one_mul]
  simp only [List.prod_cons, List.prod_nil, mul_one]
  have perm5 : ∀ a b c d e : Assn, a * (b * (c * (d * e))) = (c * b * d * e) * a :=
    fun _ _ _ _ _ => by simp only [mul_left_comm, mul_comm]
  rw [perm5]
  exact Assn.mul_le_mul_of_le le_rfl (Assn.credits_le_gc (by omega))

theorem stage1Circ_meets {w : ℕ} {p : Program} {f startIdx roundIdx : ℕ}
    {S : ℕ → ℕ → ℕ} {T_bs_max : ℕ → ℕ → ℕ → ℕ → ℕ} {T_sol : ℕ → ℕ → ℕ} {Tcb : ℕ}
    (hp : p.procs[f]? = some (stage1Circ startIdx roundIdx))
    (hstart : Meets w p startIdx ((stage1StartSpec w).withCost fun x _ => stage1StartCost x.1 x.2.1))
    (hround : Meets w p roundIdx ((stage1RoundSpec w S).withCost fun g _ =>
      stage1RoundCost T_bs_max T_sol Tcb g.I g.k)) :
    Meets w p f ((stage1CircSpec w S).withCost fun x _ =>
      stage1CircCost T_bs_max T_sol Tcb x.1 x.2.1) := by
  sep_enter ⟨I, k, capPtrs, capLimbs, costPtrs, costLimbs, outBuf⟩
    with hout2 hcp hcl hcop hcol hcapSpec hcostSpec hk h2k hkw h2mk h6m hn1 huc hsp
  rcases outBuf with _ | ⟨ob0, _ | ⟨ob1, _ | xs⟩⟩
  · simp at hout2
  · simp at hout2
  swap
  · simp at hout2
  sep_apply s1In_split_desc I k capPtrs capLimbs costPtrs costLimbs
    pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens
  sep_step
  subst m
  dsimp only [List.getElem_cons_succ, List.getElem_cons_zero]
  sep_apply (s1In_split_desc I k capPtrs capLimbs costPtrs costLimbs
    pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens).symm
  sep_step
  · -- Case `I.m = 0`
    have hm0 : I.m = 0 := by omega
    have hKcap2 : bitScalingPhases I / k + 2 = 2 := by
      have hmax0 : circMaxCapacity I = 0 :=
        Nat.eq_zero_of_le_zero (Finset.sup_le fun e _ => absurd e.isLt (by omega))
      simp [bitScalingPhases, hmax0]
    have hopt0 : I.Optimal (fun _ : Fin I.m => ((0 : ℤ) : ℝ)) := optimal_zero_of_m_eq_zero I hm0
    have hfl0 : ∀ e : Fin I.m, 0 ≤ (0 : ℤ) ∧ Limbs k ([] : List ℕ) ∧
        ([] : List ℕ).length = bitScalingPhases I / k + 2 ∧
        ((Nat.ofDigits (2 ^ k) ([] : List ℕ) : ℕ) : ℤ) = 0 :=
      fun e => absurd e.isLt (by omega)
    have hprod0 : (∏ e ∈ Finset.range I.m, Assn.list (h + e * (bitScalingPhases I / k + 2))
        (if h' : e < I.m then ([] : List ℕ) else [])) = 1 := by
      rw [hm0, Finset.range_zero, Finset.prod_empty]
    have h2w : 2 < 2 ^ w := by omega
    sep_step
    sep_step
    dsimp only [List.set]
    unfold stage1CircCost
    simp only [hm0, ↓reduceIte]
    sep_step
    let f0 : Fin I.m → ℤ := fun _ => 0
    let fl0 : Fin I.m → List ℕ := fun _ => []
    refine le_trans ?_ (Assn.mul_le_mul_of_le
      (le_iSup_of_le pIn <| le_iSup_of_le pOut <| le_iSup_of_le h <| le_iSup_of_le pTail <|
        le_iSup_of_le pHead <| le_iSup_of_le pCapPtrs <| le_iSup_of_le pCapLens <|
        le_iSup_of_le pCostSign <| le_iSup_of_le pCostPtrs <| le_iSup_of_le pCostLens <|
        le_iSup_of_le h <| le_iSup_of_le f0 <| le_iSup_of_le fl0 le_rfl) le_rfl)
    have hpure0 : [pIn, pOut, h] = [pIn, pOut, h] ∧ h ≤ h ∧ h ≤ h + stage1CircSpace I k S ∧
        I.Optimal (fun e : Fin I.m => (f0 e : ℝ)) ∧
        ∀ e : Fin I.m, 0 ≤ f0 e ∧ Limbs k (fl0 e) ∧
          (fl0 e).length = bitScalingPhases I / k + 2 ∧
          ((Nat.ofDigits (2 ^ k) (fl0 e) : ℕ) : ℤ) = f0 e :=
      ⟨rfl, le_rfl, Nat.le_add_right _ _, hopt0, hfl0⟩
    rw [eq_true hpure0, Assn.pure_true, one_mul, hprod0, mul_one, hKcap2]
    simp only [List.prod_cons, List.prod_nil, mul_one]
    rw [mul_comm ($ _)]
    refine Assn.mul_le_mul_of_le (le_of_eq (mul_assoc _ _ _).symm) (Assn.credits_le_gc (by omega))
  · -- Case `0 < I.m`
    have hm_pos : 0 < I.m := by omega
    set C := I.compress
    set K_cap := bitScalingPhases I / k + 2
    set lay := mkStage1Layout h I.n I.m K_cap
    set R := narrowCostRounds C
    set roundSp := stage1RoundBitScaleSpace C k S + stage1DualSpace C S
    set rCost := stage1RoundCost T_bs_max T_sol Tcb I k
    have hsp_eq : stage1CircSpace I k S = stage1StartSpace I k + R * roundSp := by
      unfold stage1CircSpace; simp [hm_pos.ne']; rfl
    have hsp' : h + (stage1StartSpace I k + R * roundSp) < 2 ^ w := by rw [← hsp_eq]; exact hsp
    have hstartSp_lt : h + stage1StartSpace I k < 2 ^ w := by omega
    have hsp_only : stage1CircSpace I k S < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) hsp
    have hnr_lt : R < 2 ^ w := narrowCostRounds_lt_of_space hm_pos hsp_only
    have hKk : K_cap * k < 2 ^ w := K_cap_mul_k_lt hm_pos hk h2k h2mk hsp_only
    have hresOut_eq : lay.pResOut = lay.pResIn + 9 := rfl
    have hstartSp_exp : h + (I.n + 40 + 18 * I.m + 5 * I.m * K_cap + I.m * (costScaleBits I / k + 2)) < 2 ^ w := by
      simpa only [stage1StartSpace] using hstartSp_lt
    have hresIn13 : lay.pResIn + 13 < 2 ^ w := by
      dsimp only [lay, mkStage1Layout]; omega
    have hpCapFit : lay.pCapBuf + I.m * K_cap < 2 ^ w := by
      dsimp only [lay, mkStage1Layout]
      have : 5 * I.m * K_cap = 5 * (I.m * K_cap) := Nat.mul_assoc _ _ _
      omega
    have hpFlowFit : lay.pFlow + I.m * K_cap < 2 ^ w := by
      dsimp only [lay, mkStage1Layout]
      have : 5 * I.m * K_cap = 5 * (I.m * K_cap) := Nat.mul_assoc _ _ _
      omega
    have hpResFit : lay.pResFwdBuf + I.m * K_cap < 2 ^ w := by
      dsimp only [lay, mkStage1Layout]
      have : 2 * I.m * K_cap = 2 * (I.m * K_cap) := Nat.mul_assoc _ _ _
      have : 5 * I.m * K_cap = 5 * (I.m * K_cap) := Nat.mul_assoc _ _ _
      omega
    have hpTmp1Fit : lay.pTmp1 + K_cap < 2 ^ w := by
      dsimp only [lay, mkStage1Layout]
      have h1 : K_cap ≤ I.m * K_cap := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right K_cap hm_pos
      have : 3 * I.m * K_cap = 3 * (I.m * K_cap) := Nat.mul_assoc _ _ _
      have : 5 * I.m * K_cap = 5 * (I.m * K_cap) := Nat.mul_assoc _ _ _
      omega
    have hcapPadS : ∀ e : Fin I.m, Limbs k (padLimbs K_cap (capLimbs.getD e.val [])) ∧
        (padLimbs K_cap (capLimbs.getD e.val [])).length = K_cap ∧
        Nat.ofDigits (2 ^ k) (padLimbs K_cap (capLimbs.getD e.val [])) = C.capacity e := by
      intro e
      obtain ⟨hCe, -, hve⟩ := hcapSpec e.val e.isLt
      have hlt : Nat.ofDigits (2 ^ k) (capLimbs.getD e.val []) < 2 ^ bitScalingPhases I := by
        rw [hve]
        exact lt_of_le_of_lt (Finset.le_sup (f := I.capacity) (Finset.mem_univ e))
          (Nat.lt_size_self (circMaxCapacity I))
      have hlen_le : (capLimbs.getD e.val []).length ≤ K_cap :=
        canonical_length_le_div_add_two hk hCe hlt
      refine ⟨padLimbs_limbs hCe.1, by unfold padLimbs; rw [List.length_append, List.length_replicate]; omega, ?_⟩
      unfold padLimbs; rw [ofDigits_append_replicate_zero, hve]
    -- Call `stage1Start(pIn, h)`
    sep_step from (I, k, capPtrs, capLimbs, costPtrs, costLimbs)
    -- Drop endpoint label table into `Assn.gc`
    have hdrop_tab : Assn.list (h + 37) (List.ofFn I.endpointLabels.table) ≤ Assn.gc :=
      Assn.noDebt_list _ _
    sep_apply hdrop_tab
    have hadjS_all : ∀ e : Fin I.m, Limbs k (adjLimbs.getD e.val []) ∧
        (adjLimbs.getD e.val []).length = (costLimbs.getD e.val []).length ∧
        Nat.ofDigits (2 ^ k) (adjLimbs.getD e.val []) =
          if C.cost e < 0 then (C.cost e).natAbs - 1 else (C.cost e).natAbs := by
      intro e
      have h1 : ∀ j (hj : j < I.m), Limbs k (adjLimbs.getD j []) ∧
          (adjLimbs.getD j []).length = (costLimbs.getD j []).length ∧
          Nat.ofDigits (2 ^ k) (adjLimbs.getD j []) =
            if I.cost ⟨j, hj⟩ < 0 then (I.cost ⟨j, hj⟩).natAbs - 1 else (I.cost ⟨j, hj⟩).natAbs := by
        assumption
      exact h1 e.val e.isLt
    -- Read `numRounds := mem[h + 9]` and set `j := 0`
    have hsplit_ctx0 := s1Work_split_ctx I k lay pCostSign_1 pCostLens_1 capLimbs costLimbs
      adjPtrs adjLimbs (narrowCostInitial C) (fun _ => List.replicate K_cap 0)
      (List.replicate (2 * I.m) 0) (List.replicate (2 * I.m) 0)
      (List.replicate (2 * I.m) 0) (List.replicate 4 0)
      (fun _ => List.replicate K_cap 0) (List.replicate K_cap 0) (List.replicate K_cap 0)
    rw [show lay.pCtx = h from rfl] at hsplit_ctx0
    sep_apply hsplit_ctx0
    sep_step
    subst numRounds
    dsimp only [List.getElem_cons_succ, List.getElem_cons_zero]
    sep_apply hsplit_ctx0.symm
    sep_step
    -- Split `stage1Input` to expose `pCostSign` and `pCostLens` for the round loop
    sep_apply s1In_split_loop I k capPtrs capLimbs costPtrs costLimbs
      pIn pTail_1 pHead_1 pCapPtrs_1 pCapLens_1 pCostSign_1 pCostPtrs_1 pCostLens_1
    -- Initial loop witness `t0`
    let t0 : Stage1LoopGhost I :=
      ⟨0, curH, narrowCostInitial C, fun _ => 0, fun _ => List.replicate K_cap 0,
       List.replicate (2 * I.m) 0, List.replicate (2 * I.m) 0,
       List.replicate (2 * I.m) 0, List.replicate 4 0,
       fun _ => List.replicate K_cap 0, List.replicate K_cap 0, List.replicate K_cap 0⟩
    have ht0_inv : RoundInvariantState C (costScaleBits I) t0.s t0.y :=
      roundInvariantState_zero C
    have ht0_fl : ∀ e : Fin I.m, 0 ≤ t0.s.flow e ∧ Limbs k (t0.flowLimbs e) ∧
        (t0.flowLimbs e).length = K_cap ∧
        ((Nat.ofDigits (2 ^ k) (t0.flowLimbs e) : ℕ) : ℤ) = t0.s.flow e := by
      intro e
      refine ⟨le_rfl, fun d hd => by simp [t0] at hd; subst hd; exact Nat.two_pow_pos k,
        List.length_replicate, ?_⟩
      change ((Nat.ofDigits (2 ^ k) (List.replicate K_cap 0) : ℕ) : ℤ) = 0
      rw [show List.replicate K_cap 0 = [] ++ List.replicate K_cap 0 from rfl,
          ofDigits_append_replicate_zero]
      simp
    have hcost_init : (0 : ℤ) ≤
        ↑(stage1CircCost T_bs_max T_sol Tcb I k) - 10 - ↑(stage1StartCost I k) - 13 - 1 -
          ↑((R - t0.j) * (rCost + 25) + 120) := by
      unfold stage1CircCost
      simp only [hm_pos.ne', ↓reduceIte]
      change (0 : ℤ) ≤
        ↑(stage1StartCost I k + R * (rCost + 25) + 250) - 10 - ↑(stage1StartCost I k) - 13 - 1 -
          ↑((R - 0) * (rCost + 25) + 120)
      rw [Nat.sub_zero]
      push_cast
      omega
    have ht0_j : t0.j ≤ R := Nat.zero_le R
    have ht0_curH_le : t0.curH ≤ h + stage1StartSpace I k + 0 * roundSp := by
      simpa [t0] using (by assumption : curH ≤ h + stage1StartSpace I k)
    have ht0_curH_ge : h ≤ t0.curH := by assumption
    have ht0_fr0 : ∀ e : Fin C.m, t0.s.frozen e ≠ .none → t0.s.halfCost e = 0 :=
      fun _ hne => absurd rfl hne
    -- Main loop: `while j < numRounds`
    sep_while (fun t : Stage1LoopGhost I =>
      ⟨[pIn, pOut, h, I.m, t.curH, R, t.j, 0, 0],
       t.j ≤ R ∧ h ≤ t.curH ∧ t.curH ≤ h + stage1StartSpace I k + t.j * roundSp ∧
         t.s.round = t.j ∧ RoundInvariantState C (costScaleBits I) t.s t.y ∧
         (∀ e : Fin C.m, t.s.frozen e ≠ .none → t.s.halfCost e = 0) ∧
         (∀ e : Fin I.m, 0 ≤ t.s.flow e ∧ Limbs k (t.flowLimbs e) ∧
           (t.flowLimbs e).length = K_cap ∧
           ((Nat.ofDigits (2 ^ k) (t.flowLimbs e) : ℕ) : ℤ) = t.s.flow e),
       ↑((R - t.j) * (rCost + 25) + 120),
       [Assn.list pOut [ob0, ob1],
        s1InLoopFrame I k capPtrs capLimbs costPtrs costLimbs
          pIn pTail_1 pHead_1 pCapPtrs_1 pCapLens_1 pCostSign_1 pCostPtrs_1 pCostLens_1,
        stage1WorkingAssn I k lay pCostSign_1 pCostLens_1 capLimbs costLimbs adjPtrs adjLimbs
          t.s t.flowLimbs t.resCSign t.resCMag t.resCapLens t.resOut t.resFwdLimbs t.tmp1 t.tmp2,
        Assn.list pCostSign_1 (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0),
        Assn.list pCostLens_1 (costLimbs.map List.length),
        Assn.free t.curH (2 ^ w - t.curH)]⟩)
      (fun t => R - t.j) from t0 with t
    · -- Loop body: `t.j < R`
      have hj_lt : t.j < R := by omega
      have hcurH_sp : t.curH + stage1RoundBitScaleSpace C k S + stage1DualSpace C S < 2 ^ w := by
        have hmul : (t.j + 1) * roundSp ≤ R * roundSp := Nat.mul_le_mul_right roundSp (by omega)
        rw [Nat.succ_mul] at hmul
        omega
      sep_step from ⟨I, k, t.j, lay, pCostSign_1, pCostLens_1, capLimbs, costLimbs, adjPtrs, adjLimbs,
        t.s, t.y, t.flowLimbs, t.resCSign, t.resCMag, t.resCapLens, t.resOut, t.resFwdLimbs,
        t.tmp1, t.tmp2⟩
      sep_step
      have hcurH'_le : curH_1 ≤ h + stage1StartSpace I k + (t.j + 1) * roundSp := by
        have h1 : curH_1 ≤ t.curH + stage1RoundBitScaleSpace C k S + stage1DualSpace C S := by
          assumption
        rw [Nat.succ_mul]; omega
      have hcurH'_ge : h ≤ curH_1 := le_trans hinv_1 (by assumption)
      have hsub_R : R - t.j = (R - (t.j + 1)) + 1 := by omega
      sep_exists (⟨t.j + 1, curH_1, s', y', flowLimbs', resCSign', resCMag', resCapLens', resOut',
        resFwdLimbs', tmp1', tmp2'⟩ : Stage1LoopGhost I)
    · -- Loop exit: `t.j = R`
      have hj_eq : t.j = R := by omega
      have hs_round_R : t.s.round = R := hinv_3.trans hj_eq
      have hcurH_le_R : t.curH ≤ h + stage1CircSpace I k S := by
        rw [hsp_eq]; rw [hj_eq] at hinv_2; omega
      have hoptC : C.Optimal (fun e => (t.s.flow e : ℝ)) :=
        roundInvariantState_final_optimal C t.s t.y hs_round_R hinv_4
      have hoptI : I.Optimal (fun e => (t.s.flow e : ℝ)) :=
        (I.compress_optimal_iff (fun e => (t.s.flow e : ℝ))).mp hoptC
      refine stage1Circ_exit I k capPtrs capLimbs costPtrs costLimbs
        pIn pOut h pTail_1 pHead_1 pCapPtrs_1 pCapLens_1 pCostSign_1 pCostPtrs_1 pCostLens_1
        ob0 ob1 R t _ lay rfl adjPtrs adjLimbs hinv_1 hcurH_le_R hoptI hinv_6 ?_
      omega

/-- Big-O specification of `stage1Circ` in `outer_work_compressed_bound` shape. -/
theorem stage1Circ_meetsO {w : ℕ} {p : Program} {f startIdx roundIdx : ℕ}
    {S : ℕ → ℕ → ℕ} {T_bs_max : ℕ → ℕ → ℕ → ℕ → ℕ} {T_sol : ℕ → ℕ → ℕ} {Tcb : ℕ}
    (hp : p.procs[f]? = some (stage1Circ startIdx roundIdx))
    (hstart : Meets w p startIdx ((stage1StartSpec w).withCost fun x _ => stage1StartCost x.1 x.2.1))
    (hround : Meets w p roundIdx ((stage1RoundSpec w S).withCost fun g _ =>
      stage1RoundCost T_bs_max T_sol Tcb g.I g.k)) :
    MeetsO w p f (stage1CircSpec w S) fun x _ =>
      let I := x.1
      let k := x.2.1
      let C := I.compress
      let R := narrowCostRounds C
      let T_U := bitScalingPhases I
      let L := costScaleBits I
      R * (T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            I.m * (T_U / k + 1) + C.n + 1) +
        I.m * (T_U / k + L / k + 1) + T_U + L + 1 :=
  MeetsO.of_meets (stage1Circ_meets hp hstart hround) ⟨16000 + Tcb, fun x => by
    unfold stage1CircCost
    dsimp only
    split_ifs with hm0
    · have h1 : 1 ≤ narrowCostRounds x.1.1.compress *
            (T_bs_max (bitScalingPhases x.1.1) x.1.1.compress.n x.1.1.m x.1.2.1 +
              T_sol (x.1.1.compress.n + 2) (8 * x.1.1.m + 2 * x.1.1.compress.n) +
              x.1.1.m * (bitScalingPhases x.1.1 / x.1.2.1 + 1) + x.1.1.compress.n + 1) +
          x.1.1.m * (bitScalingPhases x.1.1 / x.1.2.1 + costScaleBits x.1.1 / x.1.2.1 + 1) +
          bitScalingPhases x.1.1 + costScaleBits x.1.1 + 1 := by omega
      have h2 := Nat.mul_le_mul_left (16000 + Tcb) h1
      dsimp only [Circulation.compress] at h2 ⊢
      omega
    · set I := x.1.1
      set k := x.1.2.1
      set C := I.compress
      set R := narrowCostRounds C
      set T_U := bitScalingPhases I
      set L := costScaleBits I
      have hstart_le : stage1StartCost I k ≤
          1500 * (I.m * (T_U / k + L / k + 1) + T_U + L + 1) := by
        unfold stage1StartCost stage1StartHdrCost
        dsimp only [T_U, L]
        simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
        omega
      have hround_le : stage1RoundCost T_bs_max T_sol Tcb I k + 25 ≤
          (15700 + Tcb) * (T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            I.m * (T_U / k + 1) + C.n + 1) := by
        unfold stage1RoundCost
        dsimp only
        have hm_term : (510 * (T_U / k + 2) + Tcb + 14500) * I.m ≤
            (15700 + Tcb) * (I.m * (T_U / k + 1)) := by
          have heq : (510 * (T_U / k + 2) + Tcb + 14500) * I.m =
              I.m * (510 * (T_U / k) + (15520 + Tcb)) := by ring
          rw [heq, ← Nat.mul_assoc, Nat.mul_comm (15700 + Tcb) I.m, Nat.mul_assoc]
          apply Nat.mul_le_mul_left
          have h1 : (15700 + Tcb) * (T_U / k + 1) = (15700 + Tcb) * (T_U / k) + (15700 + Tcb) := by ring
          rw [h1]
          have h2 := Nat.mul_le_mul_right (T_U / k) (by omega : 510 ≤ 15700 + Tcb)
          omega
        have h1 := Nat.le_mul_of_pos_left (T_bs_max T_U C.n I.m k) (by omega : 0 < 15700 + Tcb)
        have h2 := Nat.le_mul_of_pos_left (T_sol (C.n + 2) (8 * I.m + 2 * C.n)) (by omega : 0 < 15700 + Tcb)
        have h3 := Nat.mul_le_mul_right C.n (by omega : 3400 ≤ 15700 + Tcb)
        dsimp only [C, T_U, Circulation.compress] at hm_term h1 h2 h3 ⊢
        simp only [Nat.mul_add, Nat.mul_one] at hm_term ⊢
        omega
      have hR_mul : R * (stage1RoundCost T_bs_max T_sol Tcb I k + 25) ≤
          (15700 + Tcb) * (R * (T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            I.m * (T_U / k + 1) + C.n + 1)) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (15700 + Tcb) R, Nat.mul_assoc]
        exact Nat.mul_le_mul_left R hround_le
      have h1500 : 1500 * (I.m * (T_U / k + L / k + 1) + T_U + L + 1) + 250 ≤
          (16000 + Tcb) * (I.m * (T_U / k + L / k + 1) + T_U + L + 1) := by
        have hge : 1 ≤ I.m * (T_U / k + L / k + 1) + T_U + L + 1 := by omega
        have hmul := Nat.mul_le_mul_right (I.m * (T_U / k + L / k + 1) + T_U + L + 1)
          (by omega : 1500 + 250 ≤ 16000 + Tcb)
        have : (1500 + 250) * (I.m * (T_U / k + L / k + 1) + T_U + L + 1) =
            1500 * (I.m * (T_U / k + L / k + 1) + T_U + L + 1) +
            250 * (I.m * (T_U / k + L / k + 1) + T_U + L + 1) := by ring
        have h250 : 250 ≤ 250 * (I.m * (T_U / k + L / k + 1) + T_U + L + 1) :=
          Nat.le_mul_of_pos_right 250 hge
        omega
      have hR2 : (15700 + Tcb) * (R * (T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            I.m * (T_U / k + 1) + C.n + 1)) ≤
          (16000 + Tcb) * (R * (T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            I.m * (T_U / k + 1) + C.n + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      set A := R * (T_bs_max T_U C.n I.m k + T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
            I.m * (T_U / k + 1) + C.n + 1)
      set B := I.m * (T_U / k + L / k + 1) + T_U + L + 1
      calc stage1StartCost I k + R * (stage1RoundCost T_bs_max T_sol Tcb I k + 25) + 250
          ≤ (1500 * B + 250) + (15700 + Tcb) * A := by omega
        _ ≤ (16000 + Tcb) * B + (16000 + Tcb) * A := Nat.add_le_add h1500 hR2
        _ = (16000 + Tcb) * (A + B) := by ring
        _ = _ := by dsimp only [A, B, C, R, T_U, L, I, k]; ring⟩

end MinCostFlow.NarrowProg.Stage1
