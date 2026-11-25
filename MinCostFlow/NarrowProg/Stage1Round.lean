module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.BitScale
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1Layout
public import MinCostFlow.NarrowProg.Stage1RoundPrep
public import MinCostFlow.NarrowProg.Stage1RoundApply
import MinCostFlow.Narrow.CostUnitsClip
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# One Stage 1 cost-scaling round (`stage1Round`, Part 5b)

Composes the six per-step dispatch helpers from `Stage1RoundPrep` and
`Stage1RoundApply` into one full Stage 1 round `stage1Round`:
1. `stage1RoundCostsCall`: compute rounded residual costs;
2. `stage1RoundResCapsCall`: compute residual forward capacities and canonical limb lengths;
3. `stage1RoundBitScaleCall`: solve the rounded residual instance with Stage 2 `bitScale`;
4. `stage1RoundDualCall`: extract the round's integral dual potential table `dy`;
5. `stage1RoundFlowCall`: augment the multi-limb flow by `delta`;
6. `stage1RoundStateCall`: advance `(frozen, halfCost)` using one cost bit and `dy`.

Preserves `stage1WorkingAssn` and `RoundInvariantState` across round `j -> j + 1`,
with explicit per-round cost `stage1RoundCost` independent of the round state `s`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate List.length_append List.length_map

/-! ### Helper lemmas for one round -/

private theorem narrowRoundedCosts_abs_le_upperClip (C : Circulation)
    (fr : Fin C.m → FreezeState) (x : Fin C.m → ℤ) (a : Fin (C.m + C.m)) :
    (narrowRoundedCosts C fr x a).natAbs ≤ upperClip C.m := by
  have hlo : lowerClip C.m ≤ upperClip C.m := lowerClip_le_upperClip C.m
  refine Fin.addCases (fun e => ?_) (fun e => ?_) a
  · simp only [narrowRoundedCosts, Fin.addCases_left, roundedForwardCost]
    cases fr e <;> simp only [clampInt] <;> omega
  · simp only [narrowRoundedCosts, Fin.addCases_right, roundedReverseCost]
    cases fr e <;> simp only [clampInt] <;> omega

private theorem stepHalfCost_frozen_zero (theta : ℕ) (fr : FreezeState) (x b d : ℤ)
    (hfr0 : fr ≠ .none → x = 0) :
    (stepHalfCost theta fr x b d).1 ≠ .none → (stepHalfCost theta fr x b d).2 = 0 := by
  cases fr with
  | pos => simp [stepHalfCost]
  | neg => simp [stepHalfCost]
  | none =>
    dsimp only [stepHalfCost]
    split_ifs <;> simp

private theorem upperClip_ge_eight {m : ℕ} (hm : 0 < m) : 8 ≤ upperClip m := by
  have h1 : (2 * m) ^ 8 ≤ lowerClip m := lowerClip_ge_pow8 m
  have h2 : lowerClip m ≤ upperClip m := lowerClip_le_upperClip m
  have h3 : 2 ^ 8 ≤ (2 * m) ^ 8 := Nat.pow_le_pow_left (by omega) 8
  omega

private theorem map_length_eq_of_getD_eq {m : ℕ} {a b : List (List ℕ)}
    (ha : a.length = m) (hb : b.length = m)
    (h : ∀ e : Fin m, (a.getD e.val []).length = (b.getD e.val []).length) :
    a.map List.length = b.map List.length := by
  refine List.ext_getElem (by simp [ha, hb]) fun i hi1 hi2 => ?_
  have him : i < m := by simp [ha] at hi1; exact hi1
  have he := h ⟨i, him⟩
  rw [List.getD_eq_getElem _ _ (by omega : i < a.length),
      List.getD_eq_getElem _ _ (by omega : i < b.length)] at he
  simpa using he

/-! ### `stage1Round` procedure, cost, and specification -/

/-- Execute one Stage 1 cost-scaling round `j`, updating `pFlow`, `pFrozen`, `pHSign`, `pHMag`,
and returning the advanced heap pointer `h2`. -/
wram_def stage1Round (rcCallIdx resCapCallIdx bsCallIdx dualCallIdx flowCallIdx stateCallIdx : ℕ)
    (pCtx, j, curH) {
  r := rcCallIdx(pCtx)
  r := resCapCallIdx(pCtx)
  h1 := bsCallIdx(pCtx, curH)
  h2 := dualCallIdx(pCtx, h1)
  r := flowCallIdx(pCtx)
  r := stateCallIdx(pCtx, j)
  return h2
}

/-- Explicit per-round cost bound for `stage1Round` (independent of the round state `s`). -/
def stage1RoundCost (T_bs_max : ℕ → ℕ → ℕ → ℕ → ℕ) (T_sol : ℕ → ℕ → ℕ) (Tcb : ℕ)
    (I : Circulation) (k : ℕ) : ℕ :=
  let C := I.compress
  let K_cap := bitScalingPhases I / k + 2
  T_bs_max (bitScalingPhases I) C.n I.m k +
    T_sol (C.n + 2) (8 * I.m + 2 * C.n) +
    (510 * K_cap + Tcb + 14500) * I.m + 3400 * C.n + 2300

/-- Ghost input bundle for `stage1RoundSpec`. -/
structure Stage1RoundArg where
  I : Circulation
  k : ℕ
  j : ℕ
  lay : Stage1Layout
  pCostSign : ℕ
  pCostLens : ℕ
  capLimbs : List (List ℕ)
  costLimbs : List (List ℕ)
  adjPtrs : List ℕ
  adjLimbs : List (List ℕ)
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

/-- Specification of `stage1Round`. -/
def stage1RoundSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Stage1RoundArg where
  pre := fun g args => ⨆ curH : ℕ,
    let C := g.I.compress
    let K_cap := bitScalingPhases g.I / g.k + 2
    ⌜args = [g.lay.pCtx, g.j, curH] ∧
      0 < g.I.m ∧
      g.s.round = g.j ∧
      RoundInvariantState C (costScaleBits g.I) g.s g.y ∧
      (∀ e : Fin C.m, g.s.frozen e ≠ .none → g.s.halfCost e = 0) ∧
      g.lay.pResOut = g.lay.pResIn + 9 ∧
      g.lay.pResIn + 13 < 2 ^ w ∧
      g.lay.pCapBuf + g.I.m * K_cap < 2 ^ w ∧
      g.lay.pFlow + g.I.m * K_cap < 2 ^ w ∧
      g.lay.pResFwdBuf + g.I.m * K_cap < 2 ^ w ∧
      g.lay.pTmp1 + K_cap < 2 ^ w ∧
      K_cap * g.k < 2 ^ w ∧
      (∀ e : Fin g.I.m, Limbs g.k (padLimbs K_cap (g.capLimbs.getD e.val [])) ∧
        (padLimbs K_cap (g.capLimbs.getD e.val [])).length = K_cap ∧
        Nat.ofDigits (2 ^ g.k) (padLimbs K_cap (g.capLimbs.getD e.val [])) = C.capacity e) ∧
      (∀ e : Fin g.I.m, Limbs g.k (g.adjLimbs.getD e.val []) ∧
        (g.adjLimbs.getD e.val []).length = (g.costLimbs.getD e.val []).length ∧
        Nat.ofDigits (2 ^ g.k) (g.adjLimbs.getD e.val []) =
          if C.cost e < 0 then (C.cost e).natAbs - 1 else (C.cost e).natAbs) ∧
      (∀ e : Fin g.I.m, 0 ≤ g.s.flow e ∧ Limbs g.k (g.flowLimbs e) ∧
        (g.flowLimbs e).length = K_cap ∧
        ((Nat.ofDigits (2 ^ g.k) (g.flowLimbs e) : ℕ) : ℤ) = g.s.flow e) ∧
      1 ≤ g.k ∧ 2 * g.k ≤ w ∧ g.k + Nat.log 2 (2 * g.k) + 2 ≤ w ∧
      2 * g.I.m + 1 < 2 ^ g.k ∧ 6 * g.I.m + 4 < 2 ^ w ∧ g.I.n + 1 < 2 ^ w ∧
      (6 * g.I.m + 21) * upperClip g.I.m < 2 ^ w ∧
      curH + stage1RoundBitScaleSpace C g.k S + stage1DualSpace C S < 2 ^ w⌝ *
    stage1WorkingAssn g.I g.k g.lay g.pCostSign g.pCostLens g.capLimbs g.costLimbs
      g.adjPtrs g.adjLimbs g.s g.flowLimbs g.resCSign g.resCMag g.resCapLens g.resOut
      g.resFwdLimbs g.tmp1 g.tmp2 *
    Assn.list g.pCostSign (List.ofFn fun e : Fin g.I.m => if g.I.cost e < 0 then 1 else 0) *
    Assn.list g.pCostLens (g.costLimbs.map List.length) *
    Assn.free curH (2 ^ w - curH)
  post := fun g args h2 => ⨆ (curH : ℕ) (s' : NarrowCostState g.I.compress)
      (y' : Fin g.I.compress.n → ℤ) (flowLimbs' : Fin g.I.m → List ℕ)
      (resCSign' : List ℕ) (resCMag' : List ℕ) (resCapLens' : List ℕ) (resOut' : List ℕ)
      (resFwdLimbs' : Fin g.I.m → List ℕ) (tmp1' : List ℕ) (tmp2' : List ℕ),
    let C := g.I.compress
    let K_cap := bitScalingPhases g.I / g.k + 2
    ⌜args = [g.lay.pCtx, g.j, curH] ∧
      curH ≤ h2 ∧ h2 ≤ curH + stage1RoundBitScaleSpace C g.k S + stage1DualSpace C S ∧
      s'.round = g.j + 1 ∧
      RoundInvariantState C (costScaleBits g.I) s' y' ∧
      (∀ e : Fin C.m, s'.frozen e ≠ .none → s'.halfCost e = 0) ∧
      (∀ e : Fin g.I.m, 0 ≤ s'.flow e ∧ Limbs g.k (flowLimbs' e) ∧
        (flowLimbs' e).length = K_cap ∧
        ((Nat.ofDigits (2 ^ g.k) (flowLimbs' e) : ℕ) : ℤ) = s'.flow e)⌝ *
    stage1WorkingAssn g.I g.k g.lay g.pCostSign g.pCostLens g.capLimbs g.costLimbs
      g.adjPtrs g.adjLimbs s' flowLimbs' resCSign' resCMag' resCapLens' resOut'
      resFwdLimbs' tmp1' tmp2' *
    Assn.list g.pCostSign (List.ofFn fun e : Fin g.I.m => if g.I.cost e < 0 then 1 else 0) *
    Assn.list g.pCostLens (g.costLimbs.map List.length) *
    Assn.free h2 (2 ^ w - h2)

private def s1MidAssn (w : ℕ) (g : Stage1RoundArg) (curH h1 : ℕ)
    (delta : Fin (g.I.m + g.I.m) → ℤ) (deltaLimbs : Fin (g.I.m + g.I.m) → List ℕ)
    (resFwd : Fin g.I.m → List ℕ) : Assn :=
  let C := g.I.compress
  let J := narrowRoundInstance C g.s
  let T_r := bitScalingPhases J
  let L_r := T_r / g.k + 2
  let K_cap := bitScalingPhases g.I / g.k + 2
  let tList := List.ofFn fun e : Fin g.I.m => (C.tail e).val
  let hList := List.ofFn fun e : Fin g.I.m => (C.head e).val
  let fwdPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pResFwdBuf + e.val * K_cap
  let revPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pFlow + e.val * K_cap
  let fwdLens := List.ofFn fun e : Fin g.I.m => canonLen (resFwd e)
  let revLens := List.ofFn fun e : Fin g.I.m => canonLen (g.flowLimbs e)
  let rho := List.ofFn fun a : Fin J.m => cappedResidual J T_r T_r delta (J.m + 1) a
  let gCap := List.ofFn fun a : Fin J.m => cappedFlow delta (J.m + 1) a
  s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
  Assn.list g.lay.pResOut [curH + 4 * g.I.m, L_r, curH, curH + 2 * g.I.m] *
  Assn.list g.lay.pResTail (tList ++ hList) *
  Assn.list g.lay.pResHead (hList ++ tList) *
  Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
    if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
  Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
    (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
  Assn.list g.lay.pResCapPtrs (fwdPtrs ++ revPtrs) *
  Assn.list g.lay.pResCapLens (fwdLens ++ revLens) *
  (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap)
    (if h : e < g.I.m then resFwd ⟨e, h⟩ else [])) *
  (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
    (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
  Assn.list curH rho *
  Assn.list (curH + 2 * g.I.m) gCap *
  (∏ a ∈ Finset.range (g.I.m + g.I.m), Assn.list (curH + 4 * g.I.m + a * L_r)
    (if h : a < g.I.m + g.I.m then deltaLimbs ⟨a, h⟩ else [])) *
  Assn.free h1 (2 ^ w - h1) *
  s1CompFixed g.I g.lay g.adjPtrs g.adjLimbs *
  s1SmallState g.I g.lay g.s *
  (∏ j ∈ Finset.range g.I.m, Assn.list (g.lay.pCapBuf + j * K_cap)
    (padLimbs K_cap (g.capLimbs.getD j []))) *
  s1Tmps g.lay g.tmp1 g.tmp2 *
  Assn.list g.pCostSign (List.ofFn fun e : Fin g.I.m => if g.I.cost e < 0 then 1 else 0) *
  Assn.list g.pCostLens (g.costLimbs.map List.length)

private theorem s1MidAssn_eq (w : ℕ) (g : Stage1RoundArg) (curH h1 : ℕ)
    (delta : Fin (g.I.m + g.I.m) → ℤ) (deltaLimbs : Fin (g.I.m + g.I.m) → List ℕ)
    (resFwd : Fin g.I.m → List ℕ) :
    let C := g.I.compress
    let J := narrowRoundInstance C g.s
    let T_r := bitScalingPhases J
    let L_r := T_r / g.k + 2
    let K_cap := bitScalingPhases g.I / g.k + 2
    let tList := List.ofFn fun e : Fin g.I.m => (C.tail e).val
    let hList := List.ofFn fun e : Fin g.I.m => (C.head e).val
    let fwdPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pResFwdBuf + e.val * K_cap
    let revPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pFlow + e.val * K_cap
    let fwdLens := List.ofFn fun e : Fin g.I.m => canonLen (resFwd e)
    let revLens := List.ofFn fun e : Fin g.I.m => canonLen (g.flowLimbs e)
    let rho := List.ofFn fun a : Fin J.m => cappedResidual J T_r T_r delta (J.m + 1) a
    let gCap := List.ofFn fun a : Fin J.m => cappedFlow delta (J.m + 1) a
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    Assn.list g.lay.pResOut [curH + 4 * g.I.m, L_r, curH, curH + 2 * g.I.m] *
    Assn.list g.lay.pResTail (tList ++ hList) *
    Assn.list g.lay.pResHead (hList ++ tList) *
    Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
      if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
    Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
      (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
    Assn.list g.lay.pResCapPtrs (fwdPtrs ++ revPtrs) *
    Assn.list g.lay.pResCapLens (fwdLens ++ revLens) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap)
      (if h : e < g.I.m then resFwd ⟨e, h⟩ else [])) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
      (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
    Assn.list curH rho *
    Assn.list (curH + 2 * g.I.m) gCap *
    (∏ a ∈ Finset.range (g.I.m + g.I.m), Assn.list (curH + 4 * g.I.m + a * L_r)
      (if h : a < g.I.m + g.I.m then deltaLimbs ⟨a, h⟩ else [])) *
    Assn.free h1 (2 ^ w - h1) *
    s1CompFixed g.I g.lay g.adjPtrs g.adjLimbs *
    s1SmallState g.I g.lay g.s *
    (∏ j ∈ Finset.range g.I.m, Assn.list (g.lay.pCapBuf + j * K_cap)
      (padLimbs K_cap (g.capLimbs.getD j []))) *
    s1Tmps g.lay g.tmp1 g.tmp2 *
    Assn.list g.pCostSign (List.ofFn fun e : Fin g.I.m => if g.I.cost e < 0 then 1 else 0) *
    Assn.list g.pCostLens (g.costLimbs.map List.length) =
    s1MidAssn w g curH h1 delta deltaLimbs resFwd := rfl

private theorem stage1Round_tail {w : ℕ} {p : Program}
    {dualCallIdx flowCallIdx stateCallIdx : ℕ}
    {S : ℕ → ℕ → ℕ} {T_bs_max : ℕ → ℕ → ℕ → ℕ → ℕ} {T_sol : ℕ → ℕ → ℕ} {Tcb : ℕ}
    (hdual : Meets w p dualCallIdx ((stage1RoundDualCallSpec w S).withCost fun g _ =>
      T_sol (g.I.compress.n + 2) (8 * g.I.m + 2 * g.I.compress.n) +
        13600 * g.I.m + 3400 * g.I.compress.n + 1520))
    (hflow : Meets w p flowCallIdx ((stage1RoundFlowCallSpec w).withCost fun g _ =>
      (190 * (bitScalingPhases g.I / g.k + 2) + 225) * g.I.m + 150))
    (hstate : Meets w p stateCallIdx ((stage1RoundStateCallSpec w).withCost fun g _ =>
      (Tcb + 210) * g.I.m + 180))
    (g : Stage1RoundArg) (curH h1 : ℕ) (rem : ℤ)
    (delta : Fin (g.I.m + g.I.m) → ℤ) (deltaLimbs : Fin (g.I.m + g.I.m) → List ℕ)
    (resFwd : Fin g.I.m → List ℕ)
    (hm_pos : 0 < g.I.m) (hround : g.s.round = g.j)
    (hinv : RoundInvariantState g.I.compress (costScaleBits g.I) g.s g.y)
    (hfr0 : ∀ e : Fin g.I.compress.m, g.s.frozen e ≠ .none → g.s.halfCost e = 0)
    (hresOut : g.lay.pResOut = g.lay.pResIn + 9) (hresIn13 : g.lay.pResIn + 13 < 2 ^ w)
    (hpFlowFit : g.lay.pFlow + g.I.m * (bitScalingPhases g.I / g.k + 2) < 2 ^ w)
    (hpTmp1Fit : g.lay.pTmp1 + (bitScalingPhases g.I / g.k + 2) < 2 ^ w)
    (hadjS : ∀ e : Fin g.I.m, Limbs g.k (g.adjLimbs.getD e.val []) ∧
      (g.adjLimbs.getD e.val []).length = (g.costLimbs.getD e.val []).length ∧
      Nat.ofDigits (2 ^ g.k) (g.adjLimbs.getD e.val []) =
        if g.I.compress.cost e < 0 then (g.I.compress.cost e).natAbs - 1 else (g.I.compress.cost e).natAbs)
    (hflS : ∀ e : Fin g.I.m, 0 ≤ g.s.flow e ∧ Limbs g.k (g.flowLimbs e) ∧
      (g.flowLimbs e).length = bitScalingPhases g.I / g.k + 2 ∧
      ((Nat.ofDigits (2 ^ g.k) (g.flowLimbs e) : ℕ) : ℤ) = g.s.flow e)
    (hk : 1 ≤ g.k) (h2k : 2 * g.k ≤ w)
    (huc : (6 * g.I.m + 21) * upperClip g.I.m < 2 ^ w)
    (hsp : curH + stage1RoundBitScaleSpace g.I.compress g.k S + stage1DualSpace g.I.compress S < 2 ^ w)
    (hcol : g.costLimbs.length = g.I.m) (hadjP : g.adjPtrs.length = g.I.m)
    (hadjL : g.adjLimbs.length = g.I.m)
    (ht1Len : g.tmp1.length = bitScalingPhases g.I / g.k + 2)
    (ht2Len : g.tmp2.length = bitScalingPhases g.I / g.k + 2)
    (hresFwdS : ∀ e : Fin g.I.m, Limbs g.k (resFwd e) ∧
      (resFwd e).length = bitScalingPhases g.I / g.k + 2 ∧
      Nat.ofDigits (2 ^ g.k) (resFwd e) = g.I.compress.capacity e - (g.s.flow e).toNat)
    (hh1_ge : curH ≤ h1)
    (hh1_le : h1 ≤ curH + bitScaleSpace (narrowRoundInstance g.I.compress g.s) g.k S)
    (hdelta_opt : (narrowRoundInstance g.I.compress g.s).Optimal (fun a => (delta a : ℝ)))
    (hdelta_spec : ∀ a : Fin (g.I.m + g.I.m), 0 ≤ delta a ∧ Limbs g.k (deltaLimbs a) ∧
      (deltaLimbs a).length = bitScalingPhases (narrowRoundInstance g.I.compress g.s) / g.k + 2 ∧
      ((Nat.ofDigits (2 ^ g.k) (deltaLimbs a) : ℕ) : ℤ) = delta a)
    (hflags_iff : ∀ a : Fin (narrowRoundInstance g.I.compress g.s).m,
      (0 < cappedResidual (narrowRoundInstance g.I.compress g.s)
          (bitScalingPhases (narrowRoundInstance g.I.compress g.s))
          (bitScalingPhases (narrowRoundInstance g.I.compress g.s)) delta
          ((narrowRoundInstance g.I.compress g.s).m + 1) a ↔
        0 < ((narrowRoundInstance g.I.compress g.s).residual delta).capacity
          (Fin.castAdd (narrowRoundInstance g.I.compress g.s).m a)) ∧
      (0 < cappedFlow delta ((narrowRoundInstance g.I.compress g.s).m + 1) a ↔
        0 < ((narrowRoundInstance g.I.compress g.s).residual delta).capacity
          (Fin.natAdd (narrowRoundInstance g.I.compress g.s).m a)))
    (hrem : ((T_sol (g.I.compress.n + 2) (8 * g.I.m + 2 * g.I.compress.n) +
        13600 * g.I.m + 3400 * g.I.compress.n + 1520 +
        ((190 * (bitScalingPhases g.I / g.k + 2) + 225) * g.I.m + 150) +
        ((Tcb + 210) * g.I.m + 180) + 50 : ℕ) : ℤ) ≤ rem) :
    SE w p stage1Round.vars
      [g.lay.pCtx, g.j, curH, 0, h1, 0] rem
      [s1MidAssn w g curH h1 delta deltaLimbs resFwd]
      (Stmt.call 5 dualCallIdx [Expr.reg 0, Expr.reg 4] ;;
       Stmt.call 3 flowCallIdx [Expr.reg 0] ;;
       Stmt.call 3 stateCallIdx [Expr.reg 0, Expr.reg 1] ;;
       Stmt.ret (Expr.reg 5))
      (fun o _ => ((stage1RoundSpec w S).withCost fun g _ =>
        stage1RoundCost T_bs_max T_sol Tcb g.I g.k).post g [g.lay.pCtx, g.j, curH] o.value) := by
  set C := g.I.compress
  set J := narrowRoundInstance C g.s
  set T_r := bitScalingPhases J
  set L_r := T_r / g.k + 2
  set K_cap := bitScalingPhases g.I / g.k + 2
  set fwdPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pResFwdBuf + e.val * K_cap
  set revPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pFlow + e.val * K_cap
  set fwdLens := List.ofFn fun e : Fin g.I.m => canonLen (resFwd e)
  set revLens := List.ofFn fun e : Fin g.I.m => canonLen (g.flowLimbs e)
  set rho := List.ofFn fun a : Fin J.m => cappedResidual J T_r T_r delta (J.m + 1) a
  set gCap := List.ofFn fun a : Fin J.m => cappedFlow delta (J.m + 1) a
  sep_apply (s1MidAssn_eq w g curH h1 delta deltaLimbs resFwd).symm
  have hCn_le : C.n ≤ 2 * g.I.m := g.I.endpointLabels_count_le
  have hCn_pos : 0 < C.n := by have := (C.tail ⟨0, hm_pos⟩).isLt; omega
  have hup8 : 8 ≤ upperClip g.I.m := upperClip_ge_eight hm_pos
  have hw8 : 8 < 2 ^ w := by
    have : 21 * 8 ≤ (6 * g.I.m + 21) * upperClip g.I.m := Nat.mul_le_mul (by omega) hup8
    omega
  have hflowFeas : ∀ e : Fin g.I.m, 0 ≤ g.s.flow e ∧ g.s.flow e ≤ (C.capacity e : ℤ) := by
    intro e; have hfe := hinv.1.2.1.2 e; dsimp only at hfe
    exact ⟨by exact_mod_cast hfe.1, by exact_mod_cast hfe.2⟩
  have hJcb_up : J.CostsBounded (upperClip g.I.m) := fun a =>
    narrowRoundedCosts_abs_le_upperClip C g.s.frozen g.s.halfCost a
  have hup_8m : upperClip g.I.m ≤ (8 * g.I.m + 2 * C.n) ^ 10 :=
    le_trans (upperClip_le_pow10 g.I.m hm_pos) (Nat.pow_le_pow_left (by omega) 10)
  have h4m_up : (4 * g.I.m + C.n + 1) * upperClip g.I.m < 2 ^ w :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega : 4 * g.I.m + C.n + 1 ≤ 6 * g.I.m + 21)) huc
  have hbsSp_le : bitScaleSpace J g.k S ≤ stage1RoundBitScaleSpace C g.k S :=
    bitScaleSpace_narrowRound_le C g.s g.k S hflowFeas
  have hrho_len : rho.length = 2 * g.I.m := by
    simp only [rho, List.length_ofFn]; change g.I.m + g.I.m = 2 * g.I.m; omega
  have hgcap_len : gCap.length = 2 * g.I.m := by
    simp only [gCap, List.length_ofFn]; change g.I.m + g.I.m = 2 * g.I.m; omega
  have hh1_dual_fit : h1 + stage1DualSpace C S < 2 ^ w := by omega
  -- Step 4: Dual extraction
  sep_step from ⟨g.I, g.k, g.lay, g.pCostSign, g.pCostLens, g.s,
    curH + 4 * g.I.m, L_r, curH, curH + 2 * g.I.m, rho, gCap⟩
  sep_apply (s1ResEp_eq g.I g.lay).symm
  have hdual_opt : (extractDualFromFlagsCall J (dualFwdFlags J rho) (dualRevFlags J gCap)).Optimal
      (fun a => (d_dual a : ℝ)) := by assumption
  set fwd := dualFwdFlags J rho
  set rev := dualRevFlags J gCap
  have hfwd_iff : ∀ a : Fin J.m, fwd a = true ↔
      0 < (J.residual delta).capacity (Fin.castAdd J.m a) := by
    intro a
    simp only [fwd, dualFwdFlags, decide_eq_true_eq, rho]
    rw [List.getD_eq_getElem _ _ (by simp [a.isLt]), List.getElem_ofFn]
    exact (hflags_iff a).1
  have hrev_iff : ∀ a : Fin J.m, rev a = true ↔
      0 < (J.residual delta).capacity (Fin.natAdd J.m a) := by
    intro a
    simp only [rev, dualRevFlags, decide_eq_true_eq, gCap]
    rw [List.getD_eq_getElem _ _ (by simp [a.isLt]), List.getElem_ofFn]
    exact (hflags_iff a).2
  have hdy_bnds0 := extractDualFromFlagsOfAnswer_bounds J (lowerClip C.m)
    (narrowRoundedCosts_lower_bound C g.s.frozen g.s.halfCost) delta fwd rev
    hfwd_iff hrev_iff hdelta_opt d_dual hdual_opt
  have hinv_next0 := roundInvariantState_step C hm_pos hCn_le (costScaleBits g.I) g.s g.y hinv
    delta hdelta_opt fwd rev hfwd_iff hrev_iff d_dual hdual_opt
  generalize extractDualFromFlagsOfAnswer J fwd rev d_dual = dy at hdy_bnds0 hinv_next0 ⊢
  -- Step 5: Flow update
  have hT_r_le : T_r ≤ bitScalingPhases g.I := bitScalingPhases_narrowRound_le C g.s hflowFeas
  have hLr_le : L_r ≤ K_cap := Nat.add_le_add_right (Nat.div_le_div_right hT_r_le) 2
  have hpDelta_fit : curH + 4 * g.I.m + 2 * g.I.m * L_r < 2 ^ w := by
    have hspJ : bitScaleSpace J g.k S =
        5 + 2 * (2 * g.I.m) + 3 * (2 * g.I.m) * L_r +
          T_r * (2 + 12 * (2 * g.I.m) + S (C.n + 1) (2 * (2 * g.I.m))) := by
      unfold bitScaleSpace
      have hm2 : J.m = 2 * g.I.m := by change g.I.m + g.I.m = 2 * g.I.m; omega
      rw [hm2]
    have h3 : 2 * g.I.m * L_r ≤ 3 * (2 * g.I.m) * L_r :=
      Nat.mul_le_mul_right L_r (by omega)
    omega
  have hflow_bnds : ∀ e : Fin g.I.m,
      (g.s.flow e).toNat + (delta (Fin.castAdd g.I.m e)).toNat < (2 ^ g.k) ^ K_cap ∧
      (delta (Fin.natAdd g.I.m e)).toNat ≤
        (g.s.flow e).toNat + (delta (Fin.castAdd g.I.m e)).toNat := by
    intro e
    have hfe := hflowFeas e
    have hdf_feas := hdelta_opt.1.2 (Fin.castAdd g.I.m e)
    have hdr_feas := hdelta_opt.1.2 (Fin.natAdd g.I.m e)
    have hdf_le : delta (Fin.castAdd g.I.m e) ≤ ((C.capacity e : ℤ) - g.s.flow e) := by
      have h1 : (delta (Fin.castAdd g.I.m e) : ℝ) ≤ (J.capacity (Fin.castAdd g.I.m e) : ℝ) := hdf_feas.2
      have h2 : delta (Fin.castAdd g.I.m e) ≤ (J.capacity (Fin.castAdd g.I.m e) : ℤ) := by
        exact_mod_cast h1
      have h3 : J.capacity (Fin.castAdd g.I.m e) = ((C.capacity e : ℤ) - g.s.flow e).toNat := by
        dsimp only [J, narrowRoundInstance, Circulation.residual]
        exact Fin.addCases_left e
      rw [h3] at h2; omega
    have hdr_le : delta (Fin.natAdd g.I.m e) ≤ g.s.flow e := by
      have h1 : (delta (Fin.natAdd g.I.m e) : ℝ) ≤ (J.capacity (Fin.natAdd g.I.m e) : ℝ) := hdr_feas.2
      have h2 : delta (Fin.natAdd g.I.m e) ≤ (J.capacity (Fin.natAdd g.I.m e) : ℤ) := by
        exact_mod_cast h1
      have h3 : J.capacity (Fin.natAdd g.I.m e) = (g.s.flow e).toNat := by
        dsimp only [J, narrowRoundInstance, Circulation.residual]
        exact Fin.addCases_right e
      rw [h3] at h2; omega
    have hcap_lt : C.capacity e < (2 ^ g.k) ^ K_cap :=
      lt_trans
        (lt_of_le_of_lt (Finset.le_sup (f := g.I.capacity) (Finset.mem_univ e))
          (Nat.lt_size_self (circMaxCapacity g.I)))
        (two_pow_lt_base_pow_Kcap hk (bitScalingPhases g.I))
    have hdf0 := (hdelta_spec (Fin.castAdd g.I.m e)).1
    have hdr0 := (hdelta_spec (Fin.natAdd g.I.m e)).1
    constructor <;> omega
  sep_apply s1Tmps_eq g.lay g.tmp1 g.tmp2
  sep_step from ⟨g.I, g.k, g.lay, g.pCostSign, g.pCostLens, g.s, g.flowLimbs, delta, deltaLimbs,
    curH + 4 * g.I.m, L_r, pDy, curH + 2 * g.I.m, g.tmp1, g.tmp2⟩
  sep_apply (s1Tmps_eq g.lay tmp1' tmp2').symm
  -- Step 6: State update
  have hdy_abs_le : ∀ v : Fin C.n, 0 ≤ dy v ∧ (dy v).natAbs ≤ upperClip g.I.m := by
    intro v
    obtain ⟨h0, hhi⟩ := hdy_bnds0 v
    have hhi' : dy v ≤ (((C.n - 1) * lowerClip g.I.m : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul] using hhi
    have hup_ge : C.n * lowerClip g.I.m ≤ upperClip g.I.m :=
      upperClip_ge_n_mul_lowerClip C.n g.I.m hCn_le
    have h1 : (C.n - 1) * lowerClip g.I.m ≤ C.n * lowerClip g.I.m :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    refine ⟨h0, by omega⟩
  have hstate_fit : ∀ e : Fin C.m,
      1 + 4 * (dy (C.head e)).natAbs + 2 * (g.s.halfCost e).natAbs < 2 ^ w ∧
      4 * (dy (C.tail e)).natAbs + 2 * (g.s.halfCost e).natAbs < 2 ^ w := by
    intro e
    have hh := (hdy_abs_le (C.head e)).2
    have ht := (hdy_abs_le (C.tail e)).2
    have hx : (g.s.halfCost e).natAbs < 8 * upperClip g.I.m := hinv.2.2.2.2 e
    have h21 : 21 * upperClip g.I.m ≤ (6 * g.I.m + 21) * upperClip g.I.m :=
      Nat.mul_le_mul_right _ (by omega)
    constructor <;> omega
  have hadj_spec' : ∀ e : Fin C.m, Limbs g.k (g.adjLimbs.getD e.val []) ∧
      Nat.ofDigits (2 ^ g.k) (g.adjLimbs.getD e.val []) =
        if C.cost e < 0 then (C.cost e).natAbs - 1 else (C.cost e).natAbs :=
    fun e => ⟨(hadjS e).1, (hadjS e).2.2⟩
  have hmap_len : g.costLimbs.map List.length = g.adjLimbs.map List.length :=
    (map_length_eq_of_getD_eq hadjL hcol (fun e => (hadjS e).2.1)).symm
  sep_apply s1CompFixed_eq g.I g.lay g.adjPtrs g.adjLimbs
  sep_apply s1SmallState_eq g.I g.lay g.s
  rw [hmap_len]
  sep_step from ⟨g.I, g.k, g.j, g.lay, g.pCostSign, g.pCostLens, g.adjPtrs, g.adjLimbs,
    g.s, dy, curH + 4 * g.I.m, L_r, pDy, curH + 2 * g.I.m⟩
  rw [← hmap_len]
  sep_apply (s1CompFixed_eq g.I g.lay g.adjPtrs g.adjLimbs).symm
  -- Fold into next `NarrowCostState`
  set s' := narrowCostStepOfAnswers C (costScaleBits g.I) g.s delta dy
  set y' : Fin C.n → ℤ := fun v => 2 * (g.y v + dy v)
  have hinv' : RoundInvariantState C (costScaleBits g.I) s' y' := hinv_next0
  have hfr0' : ∀ e : Fin C.m, s'.frozen e ≠ .none → s'.halfCost e = 0 :=
    fun e => stepHalfCost_frozen_zero (freezeThreshold C.m) (g.s.frozen e) (g.s.halfCost e) _ _ (hfr0 e)
  have hnext_fr : nextFrList C (costScaleBits g.I) g.j (freezeThreshold g.I.m) g.s.frozen g.s.halfCost dy =
      List.ofFn fun e : Fin g.I.m => freezeCode (s'.frozen e) := by
    rw [← hround]; rfl
  have hnext_hs : nextHSList C (costScaleBits g.I) g.j (freezeThreshold g.I.m) g.s.frozen g.s.halfCost dy =
      List.ofFn fun e : Fin g.I.m => if s'.halfCost e < 0 then 1 else 0 := by
    rw [← hround]; rfl
  have hnext_hm : nextHMList C (costScaleBits g.I) g.j (freezeThreshold g.I.m) g.s.frozen g.s.halfCost dy =
      List.ofFn fun e : Fin g.I.m => (s'.halfCost e).natAbs := by
    rw [← hround]; rfl
  rw [hnext_fr, hnext_hs, hnext_hm]
  sep_apply (s1SmallState_eq g.I g.lay s').symm
  set newFlowLimbs : Fin g.I.m → List ℕ := fun e =>
    updFlowLimb g.k K_cap (g.flowLimbs e)
      (deltaLimbs (Fin.castAdd g.I.m e)) (deltaLimbs (Fin.natAdd g.I.m e))
  set resCSign' := List.ofFn fun a : Fin (C.m + C.m) =>
    if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0
  set resCMag' := List.ofFn fun a : Fin (C.m + C.m) =>
    (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs
  set resCapLens' := fwdLens ++ revLens
  set resOut' := [curH + 4 * g.I.m, L_r, pDy, curH + 2 * g.I.m]
  have hnewFlow_spec : ∀ e : Fin g.I.m, 0 ≤ s'.flow e ∧ Limbs g.k (newFlowLimbs e) ∧
      (newFlowLimbs e).length = K_cap ∧
      ((Nat.ofDigits (2 ^ g.k) (newFlowLimbs e) : ℕ) : ℤ) = s'.flow e := by
    intro e
    have hfl' : Limbs g.k (newFlowLimbs e) ∧ (newFlowLimbs e).length = K_cap ∧
        ((Nat.ofDigits (2 ^ g.k) (newFlowLimbs e) : ℕ) : ℤ) =
          intAugment g.I.m g.s.flow delta e := by
      have h1 : ∀ e : Fin g.I.m, Limbs g.k (newFlowLimbs e) ∧ (newFlowLimbs e).length = K_cap ∧
          ((Nat.ofDigits (2 ^ g.k) (newFlowLimbs e) : ℕ) : ℤ) =
            intAugment g.I.m g.s.flow delta e := by assumption
      exact h1 e
    have h0 : 0 ≤ s'.flow e := by
      have hfe := (hinv'.1.2.1.2 e).1
      dsimp only at hfe
      exact_mod_cast hfe
    exact ⟨h0, hfl'.1, hfl'.2.1, hfl'.2.2⟩
  have hwork_pure : g.costLimbs.length = g.I.m ∧ g.adjPtrs.length = g.I.m ∧
      g.adjLimbs.length = g.I.m ∧ resCSign'.length = 2 * g.I.m ∧ resCMag'.length = 2 * g.I.m ∧
      resCapLens'.length = 2 * g.I.m ∧ resOut'.length = 4 ∧ tmp1'.length = K_cap ∧
      tmp2'.length = K_cap ∧ ∀ e : Fin g.I.m, (resFwd e).length = K_cap := by
    refine ⟨hcol, hadjP, hadjL, ?_, ?_, ?_, rfl, by assumption, by assumption, fun e => (hresFwdS e).2.1⟩
    · simp only [resCSign', List.length_ofFn]; change g.I.m + g.I.m = 2 * g.I.m; omega
    · simp only [resCMag', List.length_ofFn]; change g.I.m + g.I.m = 2 * g.I.m; omega
    · simp only [resCapLens', fwdLens, revLens, List.length_append, List.length_ofFn]; omega
  have hfold_work :
      s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
      Assn.list g.lay.pResOut resOut' *
      s1CompFixed g.I g.lay g.adjPtrs g.adjLimbs *
      s1SmallState g.I g.lay s' *
      s1ResEp g.I g.lay *
      Assn.list g.lay.pResCSign resCSign' *
      Assn.list g.lay.pResCMag resCMag' *
      Assn.list g.lay.pResCapPtrs (fwdPtrs ++ revPtrs) *
      Assn.list g.lay.pResCapLens resCapLens' *
      (∏ j ∈ Finset.range g.I.m, Assn.list (g.lay.pCapBuf + j * K_cap)
        (padLimbs K_cap (g.capLimbs.getD j []))) *
      (∏ j ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + j * K_cap)
        (if h : j < g.I.m then newFlowLimbs ⟨j, h⟩ else [])) *
      (∏ j ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + j * K_cap)
        (if h : j < g.I.m then resFwd ⟨j, h⟩ else [])) *
      s1Tmps g.lay tmp1' tmp2' =
      stage1WorkingAssn g.I g.k g.lay g.pCostSign g.pCostLens g.capLimbs g.costLimbs
        g.adjPtrs g.adjLimbs s' newFlowLimbs resCSign' resCMag' resCapLens' resOut'
        resFwd tmp1' tmp2' := by
    rw [stage1Working_unfold, eq_true hwork_pure, Assn.pure_true, mul_one]
  have hs'_round : s'.round = g.j + 1 := by simp [s', narrowCostStepOfAnswers, hround]
  have hh2_ge : curH ≤ h2 := le_trans hh1_ge (by assumption)
  have hh2_le_tot : h2 ≤ curH + stage1RoundBitScaleSpace C g.k S + stage1DualSpace C S := by
    have hh2_le : h2 ≤ h1 + stage1DualSpace C S := by assumption
    omega
  have hcred : (0 : ℤ) ≤
      rem - ↑(T_sol (g.I.endpointLabels.count + 2) (8 * g.I.m + 2 * g.I.endpointLabels.count) +
          13600 * g.I.m + 3400 * g.I.endpointLabels.count + 1520) - 4 -
        ↑((190 * (bitScalingPhases g.I / g.k + 2) + 225) * g.I.m + 150) - 3 -
        ↑((Tcb + 210) * g.I.m + 180) - 6 := by
    dsimp only [C, K_cap, Circulation.compress] at hrem ⊢
    omega
  sep_apply hfold_work
  sep_run
  have hpure_end : [g.lay.pCtx, g.j, curH] = [g.lay.pCtx, g.j, curH] ∧
      curH ≤ h2 ∧ h2 ≤ curH + stage1RoundBitScaleSpace C g.k S + stage1DualSpace C S ∧
      s'.round = g.j + 1 ∧ RoundInvariantState C (costScaleBits g.I) s' y' ∧
      (∀ e : Fin C.m, s'.frozen e ≠ .none → s'.halfCost e = 0) ∧
      (∀ e : Fin g.I.m, 0 ≤ s'.flow e ∧ Limbs g.k (newFlowLimbs e) ∧
        (newFlowLimbs e).length = K_cap ∧
        ((Nat.ofDigits (2 ^ g.k) (newFlowLimbs e) : ℕ) : ℤ) = s'.flow e) :=
    ⟨rfl, hh2_ge, hh2_le_tot, hs'_round, hinv', hfr0', hnewFlow_spec⟩
  refine le_trans ?_ (Assn.mul_le_mul_of_le
    (le_iSup_of_le curH <| le_iSup_of_le s' <| le_iSup_of_le y' <| le_iSup_of_le newFlowLimbs <|
      le_iSup_of_le resCSign' <| le_iSup_of_le resCMag' <| le_iSup_of_le resCapLens' <|
      le_iSup_of_le resOut' <| le_iSup_of_le resFwd <| le_iSup_of_le tmp1' <|
      le_iSup_of_le tmp2' le_rfl) le_rfl)
  rw [eq_true hpure_end, Assn.pure_true, one_mul]
  simp only [List.prod_cons, List.prod_nil, mul_one]
  rw [mul_comm ($ _)]
  refine Assn.mul_le_mul_of_le (le_of_eq ?_) (Assn.credits_le_gc hcred)
  have perm4 : ∀ a b c d : Assn, a * (b * (c * d)) = a * c * d * b := fun _ _ _ _ => by
    simp only [mul_left_comm, mul_comm]
  exact perm4 _ _ _ _

theorem stage1Round_meets {w : ℕ} {p : Program}
    {f rcCallIdx resCapCallIdx bsCallIdx dualCallIdx flowCallIdx stateCallIdx : ℕ}
    {S : ℕ → ℕ → ℕ} {T_bs : Circulation → ℕ → ℕ}
    {T_bs_max : ℕ → ℕ → ℕ → ℕ → ℕ} {T_sol : ℕ → ℕ → ℕ} {Tcb : ℕ}
    (hp : p.procs[f]? = some (stage1Round rcCallIdx resCapCallIdx bsCallIdx dualCallIdx
      flowCallIdx stateCallIdx))
    (hrc : Meets w p rcCallIdx ((stage1RoundCostsCallSpec w).withCost fun g _ => 170 * g.I.m + 120))
    (hcap : Meets w p resCapCallIdx ((stage1RoundResCapsCallSpec w).withCost fun g _ =>
      (320 * (bitScalingPhases g.I / g.k + 2) + 230) * g.I.m + 120))
    (hbs : Meets w p bsCallIdx ((stage1RoundBitScaleCallSpec w S).withCost fun g _ =>
      T_bs (narrowRoundInstance g.I.compress g.s) g.k + 40))
    (hbs_mono : ∀ (I : Circulation) (s : NarrowCostState I.compress) (k : ℕ),
      (∀ e, 0 ≤ s.flow e ∧ s.flow e ≤ (I.compress.capacity e : ℤ)) →
      T_bs (narrowRoundInstance I.compress s) k ≤ T_bs_max (bitScalingPhases I) I.compress.n I.m k)
    (hdual : Meets w p dualCallIdx ((stage1RoundDualCallSpec w S).withCost fun g _ =>
      T_sol (g.I.compress.n + 2) (8 * g.I.m + 2 * g.I.compress.n) +
        13600 * g.I.m + 3400 * g.I.compress.n + 1520))
    (hflow : Meets w p flowCallIdx ((stage1RoundFlowCallSpec w).withCost fun g _ =>
      (190 * (bitScalingPhases g.I / g.k + 2) + 225) * g.I.m + 150))
    (hstate : Meets w p stateCallIdx ((stage1RoundStateCallSpec w).withCost fun g _ =>
      (Tcb + 210) * g.I.m + 180)) :
    Meets w p f ((stage1RoundSpec w S).withCost fun g _ =>
      stage1RoundCost T_bs_max T_sol Tcb g.I g.k) := by
  sep_enter g with hm_pos hround hinv hfr0 hresOut hresIn13 hpCapFit hpFlowFit hpResFit hpTmp1Fit
    hKk hcapS hadjS hflS hk h2k hkw h2mk h6m hn1 huc hsp
  set C := g.I.compress
  set J := narrowRoundInstance C g.s
  set K_cap := bitScalingPhases g.I / g.k + 2
  have hCn_le : C.n ≤ 2 * g.I.m := g.I.endpointLabels_count_le
  have hCn1 : C.n + 1 < 2 ^ w := by omega
  have hup8 : 8 ≤ upperClip g.I.m := upperClip_ge_eight hm_pos
  have hup_lt : upperClip g.I.m < 2 ^ w := by
    have : upperClip g.I.m ≤ (6 * g.I.m + 21) * upperClip g.I.m :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hw8 : 8 < 2 ^ w := by
    have : 21 * 8 ≤ (6 * g.I.m + 21) * upperClip g.I.m :=
      Nat.mul_le_mul (by omega) hup8
    omega
  have h10m : 10 * g.I.m + 9 < 2 ^ w := by
    have hmul : (6 * g.I.m + 21) * 8 ≤ (6 * g.I.m + 21) * upperClip g.I.m :=
      Nat.mul_le_mul_left _ hup8
    omega
  have hKlt : K_cap < 2 ^ w := by
    have : K_cap ≤ K_cap * g.k := Nat.le_mul_of_pos_right _ hk
    omega
  have hflowFeas : ∀ e : Fin g.I.m, 0 ≤ g.s.flow e ∧ g.s.flow e ≤ (C.capacity e : ℤ) := by
    intro e
    have hfe := hinv.1.2.1.2 e
    dsimp only at hfe
    exact ⟨by exact_mod_cast hfe.1, by exact_mod_cast hfe.2⟩
  have hflS_rc : ∀ e : Fin g.I.m, Limbs g.k (g.flowLimbs e) ∧ (g.flowLimbs e).length = K_cap ∧
      Nat.ofDigits (2 ^ g.k) (g.flowLimbs e) = (g.s.flow e).toNat ∧
      (g.s.flow e).toNat ≤ C.capacity e := by
    intro e
    obtain ⟨h0, hL, hlen, hv⟩ := hflS e
    have hle := (hflowFeas e).2
    refine ⟨hL, hlen, by omega, by omega⟩
  have hx_lt : ∀ e : Fin C.m, (g.s.halfCost e).natAbs + 1 < 2 ^ w := by
    intro e
    have hlt : (g.s.halfCost e).natAbs < 8 * upperClip g.I.m := hinv.2.2.2.2 e
    have hmul : 8 * upperClip g.I.m ≤ (6 * g.I.m + 21) * upperClip g.I.m :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hJcb_up : J.CostsBounded (upperClip g.I.m) := fun a =>
    narrowRoundedCosts_abs_le_upperClip C g.s.frozen g.s.halfCost a
  have hup_pow10 : upperClip g.I.m ≤ (2 * g.I.m) ^ 10 := upperClip_le_pow10 g.I.m hm_pos
  have hJcb_4m : J.CostsBounded ((4 * g.I.m) ^ 10) := fun a =>
    le_trans (hJcb_up a) (le_trans hup_pow10 (Nat.pow_le_pow_left (by omega) 10))
  have hJcostW : ∀ a, (J.cost a).natAbs < 2 ^ w := fun a => lt_of_le_of_lt (hJcb_up a) hup_lt
  have hbsSp_le : bitScaleSpace J g.k S ≤ stage1RoundBitScaleSpace C g.k S :=
    bitScaleSpace_narrowRound_le C g.s g.k S hflowFeas
  have hspJ_lt : curH + bitScaleSpace (narrowRoundInstance g.I.compress g.s) g.k S < 2 ^ w := by
    change curH + bitScaleSpace J g.k S < 2 ^ w; omega
  have hbsCost_le : T_bs J g.k ≤ T_bs_max (bitScalingPhases g.I) C.n g.I.m g.k :=
    hbs_mono g.I g.s g.k hflowFeas
  sep_apply stage1Working_unfold g.I g.k g.lay g.pCostSign g.pCostLens g.capLimbs g.costLimbs
    g.adjPtrs g.adjLimbs g.s g.flowLimbs g.resCSign g.resCMag g.resCapLens g.resOut
    g.resFwdLimbs g.tmp1 g.tmp2
  have hcol : g.costLimbs.length = g.I.m := by assumption
  have hadjP : g.adjPtrs.length = g.I.m := by assumption
  have hadjL : g.adjLimbs.length = g.I.m := by assumption
  have ht1Len : g.tmp1.length = K_cap := by assumption
  have ht2Len : g.tmp2.length = K_cap := by assumption
  -- Step 1: Rounded costs
  sep_apply s1SmallState_eq g.I g.lay g.s
  sep_step from ⟨g.I, g.k, g.lay, g.pCostSign, g.pCostLens, g.s, g.resCSign, g.resCMag⟩
  sep_apply (s1SmallState_eq g.I g.lay g.s).symm
  -- Step 2: Residual capacities
  sep_step from ⟨g.I, g.k, g.lay, g.pCostSign, g.pCostLens, g.capLimbs, g.s, g.flowLimbs,
    g.resFwdLimbs, g.resCapLens⟩
  set resFwd : Fin g.I.m → List ℕ := fun e =>
    subLimbs g.k (padLimbs K_cap (g.capLimbs.getD e.val [])) (g.flowLimbs e)
  have hresFwdS : ∀ e : Fin g.I.m, Limbs g.k (resFwd e) ∧ (resFwd e).length = K_cap ∧
      Nat.ofDigits (2 ^ g.k) (resFwd e) = C.capacity e - (g.s.flow e).toNat := by assumption
  -- Step 3: Stage 2 `bitScale`
  have hflS_bs : ∀ e : Fin g.I.m, Limbs g.k (g.flowLimbs e) ∧ (g.flowLimbs e).length = K_cap ∧
      Nat.ofDigits (2 ^ g.k) (g.flowLimbs e) = (g.s.flow e).toNat :=
    fun e => ⟨(hflS_rc e).1, (hflS_rc e).2.1, (hflS_rc e).2.2.1⟩
  sep_apply s1ResEp_eq g.I g.lay
  sep_step from ⟨g.I, g.k, g.lay, g.pCostSign, g.pCostLens, g.s, g.flowLimbs, resFwd, g.resOut⟩
  sep_apply s1MidAssn_eq w g curH h1 delta deltaLimbs resFwd
  -- Hand off Steps 4-6 to `stage1Round_tail`
  have hrem_ok : ((T_sol (C.n + 2) (8 * g.I.m + 2 * C.n) +
        13600 * g.I.m + 3400 * C.n + 1520 +
        ((190 * K_cap + 225) * g.I.m + 150) +
        ((Tcb + 210) * g.I.m + 180) + 50 : ℕ) : ℤ) ≤
      ↑(stage1RoundCost T_bs_max T_sol Tcb g.I g.k) -
        ↑(170 * g.I.m + 120) - 3 -
        ↑((320 * K_cap + 230) * g.I.m + 120) - 3 -
        ↑(T_bs J g.k + 40) - 4 := by
    unfold stage1RoundCost
    have hmul : (320 * K_cap + 230) * g.I.m + (190 * K_cap + 225) * g.I.m +
        (Tcb + 210) * g.I.m + 170 * g.I.m + 13600 * g.I.m ≤
        (510 * K_cap + Tcb + 14500) * g.I.m := by
      have : (320 * K_cap + 230) * g.I.m + (190 * K_cap + 225) * g.I.m +
          (Tcb + 210) * g.I.m + 170 * g.I.m + 13600 * g.I.m =
          (510 * K_cap + Tcb + 14435) * g.I.m := by ring
      rw [this]
      exact Nat.mul_le_mul_right g.I.m (by omega)
    dsimp only [C, K_cap] at hmul hbsCost_le ⊢
    omega
  exact stage1Round_tail (T_bs_max := T_bs_max) (T_sol := T_sol) (Tcb := Tcb)
    hdual hflow hstate g curH h1 _
    delta deltaLimbs resFwd hm_pos hround hinv hfr0 hresOut hresIn13 hpFlowFit hpTmp1Fit
    hadjS hflS hk h2k huc hsp hcol hadjP hadjL ht1Len ht2Len hresFwdS
    (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) hrem_ok

/-- Big-O specification of `stage1Round`. -/
theorem stage1Round_meetsO {w : ℕ} {p : Program}
    {f rcCallIdx resCapCallIdx bsCallIdx dualCallIdx flowCallIdx stateCallIdx : ℕ}
    {S : ℕ → ℕ → ℕ} {T_bs : Circulation → ℕ → ℕ}
    {T_bs_max : ℕ → ℕ → ℕ → ℕ → ℕ} {T_sol : ℕ → ℕ → ℕ} {Tcb : ℕ}
    (hp : p.procs[f]? = some (stage1Round rcCallIdx resCapCallIdx bsCallIdx dualCallIdx
      flowCallIdx stateCallIdx))
    (hrc : Meets w p rcCallIdx ((stage1RoundCostsCallSpec w).withCost fun g _ => 170 * g.I.m + 120))
    (hcap : Meets w p resCapCallIdx ((stage1RoundResCapsCallSpec w).withCost fun g _ =>
      (320 * (bitScalingPhases g.I / g.k + 2) + 230) * g.I.m + 120))
    (hbs : Meets w p bsCallIdx ((stage1RoundBitScaleCallSpec w S).withCost fun g _ =>
      T_bs (narrowRoundInstance g.I.compress g.s) g.k + 40))
    (hbs_mono : ∀ (I : Circulation) (s : NarrowCostState I.compress) (k : ℕ),
      (∀ e, 0 ≤ s.flow e ∧ s.flow e ≤ (I.compress.capacity e : ℤ)) →
      T_bs (narrowRoundInstance I.compress s) k ≤ T_bs_max (bitScalingPhases I) I.compress.n I.m k)
    (hdual : Meets w p dualCallIdx ((stage1RoundDualCallSpec w S).withCost fun g _ =>
      T_sol (g.I.compress.n + 2) (8 * g.I.m + 2 * g.I.compress.n) +
        13600 * g.I.m + 3400 * g.I.compress.n + 1520))
    (hflow : Meets w p flowCallIdx ((stage1RoundFlowCallSpec w).withCost fun g _ =>
      (190 * (bitScalingPhases g.I / g.k + 2) + 225) * g.I.m + 150))
    (hstate : Meets w p stateCallIdx ((stage1RoundStateCallSpec w).withCost fun g _ =>
      (Tcb + 210) * g.I.m + 180)) :
    MeetsO w p f (stage1RoundSpec w S) fun g _ =>
      let C := g.I.compress
      T_bs_max (bitScalingPhases g.I) C.n g.I.m g.k +
        T_sol (C.n + 2) (8 * g.I.m + 2 * C.n) +
        g.I.m * (bitScalingPhases g.I / g.k + 1) + C.n + 1 :=
  MeetsO.of_meets (stage1Round_meets hp hrc hcap hbs hbs_mono hdual hflow hstate)
    ⟨15600 + Tcb, fun g => by
      unfold stage1RoundCost
      dsimp only
      have h1 : (510 * (bitScalingPhases g.1.I / g.1.k + 2) + Tcb + 14500) * g.1.I.m ≤
          (15600 + Tcb) * (g.1.I.m * (bitScalingPhases g.1.I / g.1.k + 1)) := by
        have hm1 : (510 * (bitScalingPhases g.1.I / g.1.k + 2) + Tcb + 14500) * g.1.I.m =
            g.1.I.m * (510 * (bitScalingPhases g.1.I / g.1.k) + (15520 + Tcb)) := by ring
        rw [hm1, ← Nat.mul_assoc, Nat.mul_comm (15600 + Tcb) g.1.I.m, Nat.mul_assoc]
        apply Nat.mul_le_mul_left
        have : (15600 + Tcb) * (bitScalingPhases g.1.I / g.1.k + 1) =
            (15600 + Tcb) * (bitScalingPhases g.1.I / g.1.k) + (15600 + Tcb) := by ring
        rw [this]
        have hle := Nat.mul_le_mul_right (bitScalingPhases g.1.I / g.1.k) (by omega : 510 ≤ 15600 + Tcb)
        omega
      have h2 : T_bs_max (bitScalingPhases g.1.I) g.1.I.compress.n g.1.I.m g.1.k ≤
          (15600 + Tcb) * T_bs_max (bitScalingPhases g.1.I) g.1.I.compress.n g.1.I.m g.1.k :=
        Nat.le_mul_of_pos_left _ (by omega)
      have h3 : T_sol (g.1.I.compress.n + 2) (8 * g.1.I.m + 2 * g.1.I.compress.n) ≤
          (15600 + Tcb) * T_sol (g.1.I.compress.n + 2) (8 * g.1.I.m + 2 * g.1.I.compress.n) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have h4 : 3400 * g.1.I.compress.n ≤ (15600 + Tcb) * g.1.I.compress.n :=
        Nat.mul_le_mul_right _ (by omega)
      dsimp only [Circulation.compress] at h1 h2 h3 h4 ⊢
      simp only [Nat.mul_add, Nat.mul_one] at h1 ⊢
      omega⟩

/-- Polymorphic module bundling the 6 round-step dispatchers and `stage1Round`. -/
def stage1RoundMod {ι : Type}
    (roundName rcCallName resCapCallName bsCallName dualCallName flowCallName stateCallName
      rcName resCapName bsName dualName flowUpdName stateUpdName : ι) : Module ι :=
  ⟨[(rcCallName, fun idx => stage1RoundCostsCall (idx rcName)),
    (resCapCallName, fun idx => stage1RoundResCapsCall (idx resCapName)),
    (bsCallName, fun idx => stage1RoundBitScaleCall (idx bsName)),
    (dualCallName, fun idx => stage1RoundDualCall (idx dualName)),
    (flowCallName, fun idx => stage1RoundFlowCall (idx flowUpdName)),
    (stateCallName, fun idx => stage1RoundStateCall (idx stateUpdName)),
    (roundName, fun idx => stage1Round (idx rcCallName) (idx resCapCallName) (idx bsCallName)
      (idx dualCallName) (idx flowCallName) (idx stateCallName))]⟩

theorem stage1RoundMod_noRand {ι : Type}
    (roundName rcCallName resCapCallName bsCallName dualCallName flowCallName stateCallName
      rcName resCapName bsName dualName flowUpdName stateUpdName : ι) :
    (stage1RoundMod roundName rcCallName resCapCallName bsCallName dualCallName flowCallName
      stateCallName rcName resCapName bsName dualName flowUpdName stateUpdName).NoRand := by
  wram_no_rand

end MinCostFlow.NarrowProg.Stage1
