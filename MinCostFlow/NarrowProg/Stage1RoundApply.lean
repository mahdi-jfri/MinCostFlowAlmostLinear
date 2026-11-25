module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1Layout
public import MinCostFlow.NarrowProg.Stage1RoundPrep
public import MinCostFlow.NarrowProg.Stage1Dual
public import MinCostFlow.NarrowProg.Stage1FlowUpdate
public import MinCostFlow.NarrowProg.Stage1StateUpdate
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Dual-extraction and update dispatch helpers for one Stage 1 round (Part 5b-2)

Three small wrapper procedures that unpack the needed pointers from the Stage 1
context header (`lay.pCtx`, `lay.pResIn`, `lay.pResOut`) and invoke:
4. `stage1RoundDualCall`: calls `stage1DualExtract`
5. `stage1RoundFlowCall`: calls `stage1FlowUpdate`
6. `stage1RoundStateCall`: calls `stage1StateUpdate`
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate List.length_append List.length_map

/-! ### 4. `stage1RoundDualCall` -/

/-- Load residual graph and presence-flag pointers and invoke `stage1DualExtract`,
overwriting `pResOut[2]` with `pDy` and discarding `pRho` / `pGCap`. -/
wram_def stage1RoundDualCall (dualIdx : ℕ) (pCtx, h1) {
  n' := mem[pCtx]
  m := mem[pCtx + 1]
  pResIn := mem[pCtx + 23]
  pResTail := mem[pResIn + 3]
  pResHead := mem[pResIn + 4]
  pResCSign := mem[pResIn + 5]
  pResCMag := mem[pResIn + 6]
  pResOut := pResIn + 9
  pRho := mem[pResOut + 2]
  pGCap := mem[pResOut + 3]
  h2 := dualIdx(n', 2 * m, pResTail, pResHead, pResCSign, pResCMag, pRho, pGCap, pResOut + 2, h1)
  return h2
}

structure S1RoundDualArg where
  I : Circulation
  k : ℕ
  lay : Stage1Layout
  pCostSign : ℕ
  pCostLens : ℕ
  s : NarrowCostState I.compress
  pDelta : ℕ
  L_r : ℕ
  pRho : ℕ
  pGCap : ℕ
  rho : List ℕ
  gCap : List ℕ

def stage1RoundDualCallSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec S1RoundDualArg where
  pre := fun g args => ⨆ h1 : ℕ,
    let C := g.I.compress
    let J := narrowRoundInstance C g.s
    let tList := List.ofFn fun e : Fin g.I.m => (C.tail e).val
    let hList := List.ofFn fun e : Fin g.I.m => (C.head e).val
    ⌜args = [g.lay.pCtx, h1] ∧ g.lay.pResOut = g.lay.pResIn + 9 ∧
      g.lay.pResIn + 13 < 2 ^ w ∧
      0 < C.n ∧ g.rho.length = 2 * g.I.m ∧ g.gCap.length = 2 * g.I.m ∧
      J.CostsBounded (upperClip g.I.m) ∧
      upperClip g.I.m ≤ (8 * g.I.m + 2 * C.n) ^ 10 ∧
      (4 * g.I.m + C.n + 1) * upperClip g.I.m < 2 ^ w ∧
      8 < 2 ^ w ∧
      h1 + stage1DualSpace C S < 2 ^ w⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    Assn.list g.lay.pResOut [g.pDelta, g.L_r, g.pRho, g.pGCap] *
    Assn.list g.lay.pResTail (tList ++ hList) *
    Assn.list g.lay.pResHead (hList ++ tList) *
    Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
      if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
    Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
      (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
    Assn.list g.pRho g.rho *
    Assn.list g.pGCap g.gCap *
    Assn.free h1 (2 ^ w - h1)
  post := fun g args h2 => ⨆ (h1 : ℕ) (pDy : ℕ)
      (d_dual : Fin (extractDualFromFlagsCall (narrowRoundInstance g.I.compress g.s)
        (dualFwdFlags (narrowRoundInstance g.I.compress g.s) g.rho)
        (dualRevFlags (narrowRoundInstance g.I.compress g.s) g.gCap)).m → ℤ),
    let C := g.I.compress
    let J := narrowRoundInstance C g.s
    let fwd := dualFwdFlags J g.rho
    let rev := dualRevFlags J g.gCap
    let Qpos := extractDualFromFlagsCall J fwd rev
    let dy := extractDualFromFlagsOfAnswer J fwd rev d_dual
    let tList := List.ofFn fun e : Fin g.I.m => (C.tail e).val
    let hList := List.ofFn fun e : Fin g.I.m => (C.head e).val
    ⌜args = [g.lay.pCtx, h1] ∧ h1 ≤ h2 ∧ h2 ≤ h1 + stage1DualSpace C S ∧
      Qpos.Optimal (fun a => (d_dual a : ℝ))⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    Assn.list g.lay.pResOut [g.pDelta, g.L_r, pDy, g.pGCap] *
    Assn.list g.lay.pResTail (tList ++ hList) *
    Assn.list g.lay.pResHead (hList ++ tList) *
    Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
      if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
    Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
      (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
    Assn.list pDy ((List.ofFn dy).flatMap encodeSignedPair) *
    Assn.free h2 (2 ^ w - h2)

private def s1DualBody (w : ℕ) (g : S1RoundDualArg) (h1 : ℕ) : Assn :=
  let C := g.I.compress
  let tList := List.ofFn fun e : Fin g.I.m => (C.tail e).val
  let hList := List.ofFn fun e : Fin g.I.m => (C.head e).val
  Assn.list g.lay.pResTail (tList ++ hList) *
  Assn.list g.lay.pResHead (hList ++ tList) *
  Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
    if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
  Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
    (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
  Assn.list g.pRho g.rho *
  Assn.list g.pGCap g.gCap *
  Assn.free h1 (2 ^ w - h1)

private theorem s1DualBody_eq (w : ℕ) (g : S1RoundDualArg) (h1 : ℕ) :
    let C := g.I.compress
    let tList := List.ofFn fun e : Fin g.I.m => (C.tail e).val
    let hList := List.ofFn fun e : Fin g.I.m => (C.head e).val
    Assn.list g.lay.pResTail (tList ++ hList) *
    Assn.list g.lay.pResHead (hList ++ tList) *
    Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
      if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
    Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
      (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
    Assn.list g.pRho g.rho *
    Assn.list g.pGCap g.gCap *
    Assn.free h1 (2 ^ w - h1) = s1DualBody w g h1 := rfl

private theorem resOut_split4 (p a b c d : ℕ) :
    Assn.list p [a, b, c, d] =
      Assn.list p [a, b] * Assn.list (p + 2) [c] * Assn.list (p + 3) [d] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one, mul_assoc,
    show p + 1 + 1 = p + 2 by omega, show p + 2 + 1 = p + 3 by omega]

theorem stage1RoundDualCall_meets {w : ℕ} {p : Program} {f dualIdx : ℕ}
    {T_sol S_sol : ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage1RoundDualCall dualIdx))
    (hdual : Meets w p dualIdx ((stage1DualExtractSpec w S_sol).withCost fun g _ =>
      T_sol (g.J.n + 2) (4 * g.J.m + 2 * g.J.n) + 6800 * g.J.m + 3400 * g.J.n + 1400)) :
    Meets w p f ((stage1RoundDualCallSpec w S_sol).withCost fun g _ =>
      T_sol (g.I.compress.n + 2) (8 * g.I.m + 2 * g.I.compress.n) +
        13600 * g.I.m + 3400 * g.I.compress.n + 1520) := by
  sep_enter g with hresOut hresIn13 hn_pos hrho hgcap hCbnd hCle hCfit hw8 hsp
  set C := g.I.compress
  set J := narrowRoundInstance C g.s
  have hJm : J.m = 2 * g.I.m := by change g.I.m + g.I.m = 2 * g.I.m; omega
  have hspJ : stage1DualExtractSpace J S_sol = stage1DualSpace C S_sol :=
    stage1DualExtractSpace_narrowRound C g.s S_sol
  have ht := (narrowRound_tail_list C g.s).symm
  have hh := (narrowRound_head_list C g.s).symm
  have h2mw : 2 * g.I.m < 2 ^ w := by
    have hup1 : 1 ≤ upperClip g.I.m := Nat.two_pow_pos _
    have h1 : 4 * g.I.m + C.n + 1 ≤ (4 * g.I.m + C.n + 1) * upperClip g.I.m :=
      Nat.le_mul_of_pos_right _ hup1
    exact lt_of_le_of_lt (by omega : 2 * g.I.m ≤ 4 * g.I.m + C.n + 1) (lt_of_le_of_lt h1 hCfit)
  have hspJ' : h1 + stage1DualExtractSpace J S_sol < 2 ^ w := by rw [hspJ]; exact hsp
  have hCfit' : (2 * J.m + J.n + 1) * upperClip g.I.m < 2 ^ w := by
    rw [hJm]; simpa only [show 2 * (2 * g.I.m) = 4 * g.I.m by omega] using hCfit
  have hCle' : upperClip g.I.m ≤ (4 * J.m + 2 * J.n) ^ 10 := by
    rw [hJm, show 4 * (2 * g.I.m) = 8 * g.I.m by omega]; exact hCle
  have hrho' : g.rho.length = J.m := by rw [hJm]; exact hrho
  have hgcap' : g.gCap.length = J.m := by rw [hJm]; exact hgcap
  sep_apply s1DualBody_eq w g h1
  sep_apply s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens
  sep_apply resOut_split4 g.lay.pResOut g.pDelta g.L_r g.pRho g.pGCap
  iterate 3 sep_step
  subst n' m pResIn
  dsimp only [List.getElem_cons_succ, List.getElem_cons_zero]
  iterate 5 sep_step
  subst pResTail pResHead pResCSign pResCMag pResOut
  dsimp only [List.getElem_cons_succ, List.getElem_cons_zero]
  rw [← hresOut]
  iterate 2 sep_step
  subst pRho pGCap
  sep_apply (s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens).symm
  sep_apply (s1DualBody_eq w g h1).symm
  rw [ht, hh]
  have hJn : J.n = C.n := rfl
  have hcost_dual : T_sol (J.n + 2) (4 * J.m + 2 * J.n) + 6800 * J.m + 3400 * J.n + 1400 =
      T_sol (C.n + 2) (8 * g.I.m + 2 * C.n) + 13600 * g.I.m + 3400 * C.n + 1400 := by
    rw [hJm, hJn]
    have h8 : 4 * (2 * g.I.m) = 8 * g.I.m := by omega
    rw [h8]; omega
  sep_step from ⟨J, upperClip g.I.m, g.rho, g.gCap, g.pRho⟩
  rw [← ht, ← hh]
  sep_apply (resOut_split4 g.lay.pResOut g.pDelta g.L_r pDy g.pGCap).symm
  sep_run
  · dsimp only [C, Circulation.compress] at hcost_dual; rw [hcost_dual]; omega
  · rwa [← hspJ]

/-! ### 5. `stage1RoundFlowCall` -/

/-- Load flow and delta pointers and invoke `stage1FlowUpdate`, discarding `pDelta`. -/
wram_def stage1RoundFlowCall (flowUpdIdx : ℕ) (pCtx) {
  m := mem[pCtx + 1]
  k := mem[pCtx + 2]
  Kcap := mem[pCtx + 5]
  pFlow := mem[pCtx + 16]
  pTmp1 := mem[pCtx + 18]
  pTmp2 := mem[pCtx + 19]
  pResIn := mem[pCtx + 23]
  pResOut := pResIn + 9
  pDelta := mem[pResOut]
  Lround := mem[pResOut + 1]
  r := flowUpdIdx(m, k, Kcap, Lround, pFlow, pDelta, pTmp1, pTmp2)
  return 0
}

structure S1RoundFlowArg where
  I : Circulation
  k : ℕ
  lay : Stage1Layout
  pCostSign : ℕ
  pCostLens : ℕ
  s : NarrowCostState I.compress
  flowLimbs : Fin I.m → List ℕ
  delta : Fin (I.m + I.m) → ℤ
  deltaLimbs : Fin (I.m + I.m) → List ℕ
  pDelta : ℕ
  L_r : ℕ
  pDy : ℕ
  pGCap : ℕ
  tmp1 : List ℕ
  tmp2 : List ℕ

def stage1RoundFlowCallSpec (w : ℕ) : Spec S1RoundFlowArg where
  pre := fun g args =>
    let K_cap := bitScalingPhases g.I / g.k + 2
    ⌜args = [g.lay.pCtx] ∧ g.lay.pResOut = g.lay.pResIn + 9 ∧
      g.lay.pResIn + 13 < 2 ^ w ∧
      1 ≤ g.k ∧ 2 * g.k ≤ w ∧ g.L_r ≤ K_cap ∧
      g.tmp1.length = K_cap ∧ g.tmp2.length = K_cap ∧
      g.lay.pTmp1 + K_cap < 2 ^ w ∧
      g.lay.pFlow + g.I.m * K_cap < 2 ^ w ∧
      g.pDelta + 2 * g.I.m * g.L_r < 2 ^ w ∧
      (∀ e : Fin g.I.m, 0 ≤ g.s.flow e ∧ Limbs g.k (g.flowLimbs e) ∧
        (g.flowLimbs e).length = K_cap ∧
        ((Nat.ofDigits (2 ^ g.k) (g.flowLimbs e) : ℕ) : ℤ) = g.s.flow e) ∧
      (∀ a : Fin (g.I.m + g.I.m), 0 ≤ g.delta a ∧ Limbs g.k (g.deltaLimbs a) ∧
        (g.deltaLimbs a).length = g.L_r ∧
        ((Nat.ofDigits (2 ^ g.k) (g.deltaLimbs a) : ℕ) : ℤ) = g.delta a) ∧
      (∀ e : Fin g.I.m,
        (g.s.flow e).toNat + (g.delta (Fin.castAdd g.I.m e)).toNat < (2 ^ g.k) ^ K_cap ∧
        (g.delta (Fin.natAdd g.I.m e)).toNat ≤
          (g.s.flow e).toNat + (g.delta (Fin.castAdd g.I.m e)).toNat)⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    Assn.list g.lay.pResOut [g.pDelta, g.L_r, g.pDy, g.pGCap] *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
      (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
    (∏ a ∈ Finset.range (g.I.m + g.I.m), Assn.list (g.pDelta + a * g.L_r)
      (if h : a < g.I.m + g.I.m then g.deltaLimbs ⟨a, h⟩ else [])) *
    Assn.list g.lay.pTmp1 g.tmp1 *
    Assn.list g.lay.pTmp2 g.tmp2
  post := fun g args v => ⨆ (tmp1' : List ℕ) (tmp2' : List ℕ),
    let K_cap := bitScalingPhases g.I / g.k + 2
    let newLimbs : Fin g.I.m → List ℕ := fun e =>
      updFlowLimb g.k K_cap (g.flowLimbs e)
        (g.deltaLimbs (Fin.castAdd g.I.m e)) (g.deltaLimbs (Fin.natAdd g.I.m e))
    ⌜args = [g.lay.pCtx] ∧ v = 0 ∧
      tmp1'.length = K_cap ∧ tmp2'.length = K_cap ∧
      (∀ e : Fin g.I.m, Limbs g.k (newLimbs e) ∧ (newLimbs e).length = K_cap ∧
        ((Nat.ofDigits (2 ^ g.k) (newLimbs e) : ℕ) : ℤ) =
          intAugment g.I.m g.s.flow g.delta e)⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    Assn.list g.lay.pResOut [g.pDelta, g.L_r, g.pDy, g.pGCap] *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
      (if h : e < g.I.m then newLimbs ⟨e, h⟩ else [])) *
    Assn.list g.lay.pTmp1 tmp1' *
    Assn.list g.lay.pTmp2 tmp2'

private def s1FlowBody (g : S1RoundFlowArg) : Assn :=
  let K_cap := bitScalingPhases g.I / g.k + 2
  (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
    (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
  (∏ a ∈ Finset.range (g.I.m + g.I.m), Assn.list (g.pDelta + a * g.L_r)
    (if h : a < g.I.m + g.I.m then g.deltaLimbs ⟨a, h⟩ else [])) *
  Assn.list g.lay.pTmp1 g.tmp1 *
  Assn.list g.lay.pTmp2 g.tmp2

private theorem s1FlowBody_eq (g : S1RoundFlowArg) :
    let K_cap := bitScalingPhases g.I / g.k + 2
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
      (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
    (∏ a ∈ Finset.range (g.I.m + g.I.m), Assn.list (g.pDelta + a * g.L_r)
      (if h : a < g.I.m + g.I.m then g.deltaLimbs ⟨a, h⟩ else [])) *
    Assn.list g.lay.pTmp1 g.tmp1 *
    Assn.list g.lay.pTmp2 g.tmp2 = s1FlowBody g := rfl

theorem stage1RoundFlowCall_meets {w : ℕ} {p : Program} {f flowUpdIdx : ℕ}
    (hp : p.procs[f]? = some (stage1RoundFlowCall flowUpdIdx))
    (hfu : Meets w p flowUpdIdx ((stage1FlowUpdateSpec w).withCost fun inp _ =>
      (190 * inp.K_cap + 225) * inp.m + 50)) :
    Meets w p f ((stage1RoundFlowCallSpec w).withCost fun g _ =>
      (190 * (bitScalingPhases g.I / g.k + 2) + 225) * g.I.m + 150) := by
  sep_enter g with hresOut hresIn13 hk h2k hLle ht1 ht2 ht1f hff hdf hflS hdlS hbnd
  set K_cap := bitScalingPhases g.I / g.k + 2
  sep_apply s1FlowBody_eq g
  sep_apply s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens
  iterate 7 sep_step
  subst m k Kcap pFlow pTmp1 pTmp2 pResIn
  dsimp only [List.getElem_cons_succ, List.getElem_cons_zero]
  sep_step
  subst pResOut
  rw [← hresOut]
  iterate 2 sep_step
  subst pDelta Lround
  sep_apply (s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens).symm
  sep_apply (s1FlowBody_eq g).symm
  sep_step from ⟨g.I.m, g.k, K_cap, g.L_r, g.s.flow, g.flowLimbs, g.delta, g.deltaLimbs, g.tmp1, g.tmp2⟩
  have hdrop : (∏ a ∈ Finset.range (g.I.m + g.I.m), Assn.list (g.pDelta + a * g.L_r)
      (if h : a < g.I.m + g.I.m then g.deltaLimbs ⟨a, h⟩ else [])) ≤ Assn.gc :=
    Assn.noDebt_prod _ fun _ _ => Assn.noDebt_list _ _
  sep_apply hdrop
  sep_run

/-! ### 6. `stage1RoundStateCall` -/

/-- Load pointers from `pCtx` and `pResOut`, invoke `stage1StateUpdate`, and discard `pDy`. -/
wram_def stage1RoundStateCall (stateUpdIdx : ℕ) (pCtx, j) {
  m := mem[pCtx + 1]
  k := mem[pCtx + 2]
  L := mem[pCtx + 3]
  theta := mem[pCtx + 8]
  pCompTail := mem[pCtx + 10]
  pCompHead := mem[pCtx + 11]
  pCostSign := mem[pCtx + 12]
  pCostLens := mem[pCtx + 13]
  pAdjPtrs := mem[pCtx + 14]
  pFrozen := mem[pCtx + 20]
  pHSign := mem[pCtx + 21]
  pHMag := mem[pCtx + 22]
  pResIn := mem[pCtx + 23]
  pResIn := pResIn + 9
  pDy := mem[pResIn + 2]
  r := stateUpdIdx(m, k, L, j, theta, pCompTail, pCompHead, pCostSign, pAdjPtrs, pCostLens,
    pFrozen, pHSign, pHMag, pDy)
  return 0
}

structure S1RoundStateArg where
  I : Circulation
  k : ℕ
  j : ℕ
  lay : Stage1Layout
  pCostSign : ℕ
  pCostLens : ℕ
  adjPtrs : List ℕ
  adjLimbs : List (List ℕ)
  s : NarrowCostState I.compress
  dy : Fin I.compress.n → ℤ
  pDelta : ℕ
  L_r : ℕ
  pDy : ℕ
  pGCap : ℕ

def stage1RoundStateCallSpec (w : ℕ) : Spec S1RoundStateArg where
  pre := fun g args =>
    let C := g.I.compress
    ⌜args = [g.lay.pCtx, g.j] ∧ g.lay.pResOut = g.lay.pResIn + 9 ∧
      g.lay.pResIn + 13 < 2 ^ w ∧
      g.adjPtrs.length = g.I.m ∧ g.adjLimbs.length = g.I.m ∧
      1 ≤ g.k ∧ 4 < 2 ^ w ∧
      (∀ e : Fin C.m, Limbs g.k (g.adjLimbs.getD e.val []) ∧
        Nat.ofDigits (2 ^ g.k) (g.adjLimbs.getD e.val []) =
          if C.cost e < 0 then (C.cost e).natAbs - 1 else (C.cost e).natAbs) ∧
      (∀ v : Fin C.n, 0 ≤ g.dy v) ∧
      (∀ e : Fin C.m,
        1 + 4 * (g.dy (C.head e)).natAbs + 2 * (g.s.halfCost e).natAbs < 2 ^ w ∧
        4 * (g.dy (C.tail e)).natAbs + 2 * (g.s.halfCost e).natAbs < 2 ^ w) ∧
      (∀ e : Fin C.m, g.s.frozen e ≠ .none → g.s.halfCost e = 0)⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    Assn.list g.lay.pResOut [g.pDelta, g.L_r, g.pDy, g.pGCap] *
    Assn.list g.lay.pCompTail (List.ofFn fun e : Fin C.m => (C.tail e).val) *
    Assn.list g.lay.pCompHead (List.ofFn fun e : Fin C.m => (C.head e).val) *
    Assn.list g.pCostSign (List.ofFn fun e : Fin C.m => if C.cost e < 0 then 1 else 0) *
    Assn.list g.lay.pAdjCostPtrs g.adjPtrs *
    Assn.list g.pCostLens (g.adjLimbs.map List.length) *
    (∏ e ∈ Finset.range C.m, Assn.list (g.adjPtrs.getD e 0) (g.adjLimbs.getD e [])) *
    Assn.list g.lay.pFrozen (List.ofFn fun e : Fin C.m => freezeCode (g.s.frozen e)) *
    Assn.list g.lay.pHSign (List.ofFn fun e : Fin C.m => if g.s.halfCost e < 0 then 1 else 0) *
    Assn.list g.lay.pHMag (List.ofFn fun e : Fin C.m => (g.s.halfCost e).natAbs) *
    Assn.list g.pDy ((List.ofFn g.dy).flatMap encodeSignedPair)
  post := fun g args v =>
    let C := g.I.compress
    ⌜args = [g.lay.pCtx, g.j] ∧ v = 0⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    Assn.list g.lay.pResOut [g.pDelta, g.L_r, g.pDy, g.pGCap] *
    Assn.list g.lay.pCompTail (List.ofFn fun e : Fin C.m => (C.tail e).val) *
    Assn.list g.lay.pCompHead (List.ofFn fun e : Fin C.m => (C.head e).val) *
    Assn.list g.pCostSign (List.ofFn fun e : Fin C.m => if C.cost e < 0 then 1 else 0) *
    Assn.list g.lay.pAdjCostPtrs g.adjPtrs *
    Assn.list g.pCostLens (g.adjLimbs.map List.length) *
    (∏ e ∈ Finset.range C.m, Assn.list (g.adjPtrs.getD e 0) (g.adjLimbs.getD e [])) *
    Assn.list g.lay.pFrozen
      (nextFrList C (costScaleBits g.I) g.j (freezeThreshold g.I.m) g.s.frozen g.s.halfCost g.dy) *
    Assn.list g.lay.pHSign
      (nextHSList C (costScaleBits g.I) g.j (freezeThreshold g.I.m) g.s.frozen g.s.halfCost g.dy) *
    Assn.list g.lay.pHMag
      (nextHMList C (costScaleBits g.I) g.j (freezeThreshold g.I.m) g.s.frozen g.s.halfCost g.dy)

private def s1StateBody (g : S1RoundStateArg) : Assn :=
  let C := g.I.compress
  Assn.list g.lay.pCompTail (List.ofFn fun e : Fin C.m => (C.tail e).val) *
  Assn.list g.lay.pCompHead (List.ofFn fun e : Fin C.m => (C.head e).val) *
  Assn.list g.pCostSign (List.ofFn fun e : Fin C.m => if C.cost e < 0 then 1 else 0) *
  Assn.list g.lay.pAdjCostPtrs g.adjPtrs *
  Assn.list g.pCostLens (g.adjLimbs.map List.length) *
  (∏ e ∈ Finset.range C.m, Assn.list (g.adjPtrs.getD e 0) (g.adjLimbs.getD e [])) *
  Assn.list g.lay.pFrozen (List.ofFn fun e : Fin C.m => freezeCode (g.s.frozen e)) *
  Assn.list g.lay.pHSign (List.ofFn fun e : Fin C.m => if g.s.halfCost e < 0 then 1 else 0) *
  Assn.list g.lay.pHMag (List.ofFn fun e : Fin C.m => (g.s.halfCost e).natAbs) *
  Assn.list g.pDy ((List.ofFn g.dy).flatMap encodeSignedPair)

private theorem s1StateBody_eq (g : S1RoundStateArg) :
    let C := g.I.compress
    Assn.list g.lay.pCompTail (List.ofFn fun e : Fin C.m => (C.tail e).val) *
    Assn.list g.lay.pCompHead (List.ofFn fun e : Fin C.m => (C.head e).val) *
    Assn.list g.pCostSign (List.ofFn fun e : Fin C.m => if C.cost e < 0 then 1 else 0) *
    Assn.list g.lay.pAdjCostPtrs g.adjPtrs *
    Assn.list g.pCostLens (g.adjLimbs.map List.length) *
    (∏ e ∈ Finset.range C.m, Assn.list (g.adjPtrs.getD e 0) (g.adjLimbs.getD e [])) *
    Assn.list g.lay.pFrozen (List.ofFn fun e : Fin C.m => freezeCode (g.s.frozen e)) *
    Assn.list g.lay.pHSign (List.ofFn fun e : Fin C.m => if g.s.halfCost e < 0 then 1 else 0) *
    Assn.list g.lay.pHMag (List.ofFn fun e : Fin C.m => (g.s.halfCost e).natAbs) *
    Assn.list g.pDy ((List.ofFn g.dy).flatMap encodeSignedPair) = s1StateBody g := rfl

theorem stage1RoundStateCall_meets {w : ℕ} {p : Program} {f stateUpdIdx : ℕ} {Tcb : ℕ}
    (hp : p.procs[f]? = some (stage1RoundStateCall stateUpdIdx))
    (hsu : Meets w p stateUpdIdx ((stage1StateUpdateSpec w).withCost fun g _ =>
      (Tcb + 210) * g.C.m + 30)) :
    Meets w p f ((stage1RoundStateCallSpec w).withCost fun g _ =>
      (Tcb + 210) * g.I.m + 180) := by
  sep_enter g with hresOut hresIn13 hap hal hk hw4 hadj hdy0 hfit hfr0
  sep_apply s1StateBody_eq g
  sep_apply s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens
  iterate 13 sep_step
  subst m k L theta pCompTail pCompHead pCostSign pCostLens pAdjPtrs pFrozen pHSign pHMag pResIn
  dsimp only [List.getElem_cons_succ, List.getElem_cons_zero]
  sep_step
  subst pResIn
  rw [← hresOut]
  sep_step
  subst pDy
  sep_apply (s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens).symm
  sep_apply (s1StateBody_eq g).symm
  sep_step from ⟨g.I.compress, g.k, costScaleBits g.I, g.j, freezeThreshold g.I.m,
    g.s.frozen, g.s.halfCost, g.dy, g.adjPtrs, g.adjLimbs⟩
  sep_run

/-! ### Working-assertion bundles for `stage1Round` -/

private lemma perm21 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 : Assn} :
    a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 *
      a18 * a19 * a20 * a21 =
    (a1 * a2) * a3 * (a4 * a5 * a6 * a7) * (a8 * a9 * a10) * (a11 * a12) * a13 * a14 * a15 * a16 *
      a17 * a18 * a19 * (a20 * a21) := by
  simp only [mul_assoc]

def s1CompFixed (I : Circulation) (lay : Stage1Layout)
    (adjPtrs : List ℕ) (adjLimbs : List (List ℕ)) : Assn :=
  let C := I.compress
  Assn.list lay.pCompTail (List.ofFn fun e : Fin I.m => (C.tail e).val) *
  Assn.list lay.pCompHead (List.ofFn fun e : Fin I.m => (C.head e).val) *
  Assn.list lay.pAdjCostPtrs adjPtrs *
  (∏ j ∈ Finset.range I.m, Assn.list (adjPtrs.getD j 0) (adjLimbs.getD j []))

def s1SmallState (I : Circulation) (lay : Stage1Layout) (s : NarrowCostState I.compress) : Assn :=
  Assn.list lay.pFrozen (List.ofFn fun e : Fin I.m => freezeCode (s.frozen e)) *
  Assn.list lay.pHSign (List.ofFn fun e : Fin I.m => if s.halfCost e < 0 then 1 else 0) *
  Assn.list lay.pHMag (List.ofFn fun e : Fin I.m => (s.halfCost e).natAbs)

def s1ResEp (I : Circulation) (lay : Stage1Layout) : Assn :=
  let C := I.compress
  let tList := List.ofFn fun e : Fin I.m => (C.tail e).val
  let hList := List.ofFn fun e : Fin I.m => (C.head e).val
  Assn.list lay.pResTail (tList ++ hList) *
  Assn.list lay.pResHead (hList ++ tList)

def s1Tmps (lay : Stage1Layout) (tmp1 tmp2 : List ℕ) : Assn :=
  Assn.list lay.pTmp1 tmp1 * Assn.list lay.pTmp2 tmp2

theorem s1CompFixed_eq (I : Circulation) (lay : Stage1Layout)
    (adjPtrs : List ℕ) (adjLimbs : List (List ℕ)) :
    let C := I.compress
    s1CompFixed I lay adjPtrs adjLimbs =
      Assn.list lay.pCompTail (List.ofFn fun e : Fin I.m => (C.tail e).val) *
      Assn.list lay.pCompHead (List.ofFn fun e : Fin I.m => (C.head e).val) *
      Assn.list lay.pAdjCostPtrs adjPtrs *
      (∏ j ∈ Finset.range I.m, Assn.list (adjPtrs.getD j 0) (adjLimbs.getD j [])) := rfl

theorem s1SmallState_eq (I : Circulation) (lay : Stage1Layout) (s : NarrowCostState I.compress) :
    s1SmallState I lay s =
      Assn.list lay.pFrozen (List.ofFn fun e : Fin I.m => freezeCode (s.frozen e)) *
      Assn.list lay.pHSign (List.ofFn fun e : Fin I.m => if s.halfCost e < 0 then 1 else 0) *
      Assn.list lay.pHMag (List.ofFn fun e : Fin I.m => (s.halfCost e).natAbs) := rfl

theorem s1ResEp_eq (I : Circulation) (lay : Stage1Layout) :
    let C := I.compress
    let tList := List.ofFn fun e : Fin I.m => (C.tail e).val
    let hList := List.ofFn fun e : Fin I.m => (C.head e).val
    s1ResEp I lay =
      Assn.list lay.pResTail (tList ++ hList) *
      Assn.list lay.pResHead (hList ++ tList) := rfl

theorem s1Tmps_eq (lay : Stage1Layout) (tmp1 tmp2 : List ℕ) :
    s1Tmps lay tmp1 tmp2 = Assn.list lay.pTmp1 tmp1 * Assn.list lay.pTmp2 tmp2 := rfl

theorem stage1Working_unfold (I : Circulation) (k : ℕ) (lay : Stage1Layout)
    (pCostSign pCostLens : ℕ) (capLimbs costLimbs : List (List ℕ))
    (adjPtrs : List ℕ) (adjLimbs : List (List ℕ))
    (s : NarrowCostState I.compress) (flowLimbs : Fin I.m → List ℕ)
    (resCSign resCMag resCapLens resOut : List ℕ)
    (resFwdLimbs : Fin I.m → List ℕ) (tmp1 tmp2 : List ℕ) :
    let K_cap := bitScalingPhases I / k + 2
    let fwdPtrs := List.ofFn fun e : Fin I.m => lay.pResFwdBuf + e.val * K_cap
    let revPtrs := List.ofFn fun e : Fin I.m => lay.pFlow + e.val * K_cap
    stage1WorkingAssn I k lay pCostSign pCostLens capLimbs costLimbs adjPtrs adjLimbs
      s flowLimbs resCSign resCMag resCapLens resOut resFwdLimbs tmp1 tmp2 =
    s1CtxHdr I k lay pCostSign pCostLens *
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
      (∀ e : Fin I.m, (resFwdLimbs e).length = K_cap)⌝ := by
  unfold stage1WorkingAssn s1CtxHdr s1CompFixed s1SmallState s1ResEp s1Tmps
  dsimp only
  congr 1
  exact perm21

end MinCostFlow.NarrowProg.Stage1
