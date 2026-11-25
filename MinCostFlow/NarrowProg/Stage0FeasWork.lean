module

public import MinCostFlow.NarrowProg.Stage0FeasPost
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 4: pruned feasibility call (`stage0Feas`) and polymorphic `stage0FeasMod`

Allocates `stage0FeasSpace m L = 27 * m + m * L + 12` words from `Assn.free h (2 ^ w - h)`,
builds the pruned feasibility circulation `P' = (buildFeasibilityInstance I hv).withoutZeroEdges`,
splits `pShCapBuf * pShDemBuf` into `stage1Input P'` via `feas_split_shCap_shDem`, invokes
`stage1Circ`, runs `stage0FeasPost` (saturation check + conditional scatter into `pFeasFlow`),
restores `pShCapBuf * pShDemBuf` intact, and writes `[ok, pFeasFlow]` to `pFeasOut`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow
open MinCostFlow.NarrowProg.Stage1

namespace MinCostFlow.NarrowProg

/-! ### Space budget and heap split -/

/-- Exact heap space allocated by `stage0Feas` before calling `stage1Circ` (`25 * m + m * L + 12`). -/
def stage0FeasSpace (m L : ℕ) : ℕ :=
  10 + 2 + 8 * (3 * m) + m + m * L

theorem stage0FeasSpace_eq (m L : ℕ) :
    stage0FeasSpace m L = 25 * m + m * L + 12 := by
  unfold stage0FeasSpace; ring

theorem split_free_feas {h m L w : ℕ}
    (hfit : h + stage0FeasSpace m L < 2 ^ w) :
    let cap := 3 * m
    Assn.free h (2 ^ w - h) ≤
      Assn.list h (List.replicate 10 0) *
      Assn.list (h + 10) (List.replicate 2 0) *
      Assn.list (h + 10 + 2) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap + cap + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap) (List.replicate m 0) *
      Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + m) (List.replicate cap 0) *
      (∏ e ∈ Finset.range m,
        Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + m + cap + e * L)
          (List.replicate L 0)) *
      Assn.free (h + stage0FeasSpace m L) (2 ^ w - (h + stage0FeasSpace m L)) := by
  dsimp only
  set cap := 3 * m
  have hsp : h + stage0FeasSpace m L =
      h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + m + cap + m * L := by
    unfold stage0FeasSpace; ring
  rw [hsp]
  have hfit' : h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + m + cap + m * L < 2 ^ w :=
    hsp ▸ hfit
  rw [show 2 ^ w - h = 10 + (2 ^ w - (h + 10)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10) = 2 + (2 ^ w - (h + 10 + 2)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2) = cap + (2 ^ w - (h + 10 + 2 + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap) = m + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + m)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + m) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + m + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + m + cap) = m * L + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + m + cap + m * L)) by omega, Assn.free_add',
      free_to_prod_replicate]
  simp only [← mul_assoc]
  exact le_refl _

/-- Transparent wrapper around an `Assn` variable so `sep_apply` matches it by head constant
without unfolding its contents. -/
def holdAssn (A : Assn) : Assn := A

/-- The non-capacity arrays of `stage1Input` (header-pointed tail, head, and cost tables + limbs),
bundled so `stage0FeasRun` can discard them into `Assn.gc` in one step after `stage1Circ`. -/
private def stage1InputRest (P' : Circulation) (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pTail pHead pCostSign pCostPtrs pCostLens : ℕ) : Assn :=
  Assn.list pTail (List.ofFn fun e : Fin P'.m => (P'.tail e).val) *
  Assn.list pHead (List.ofFn fun e : Fin P'.m => (P'.head e).val) *
  Assn.list pCostSign (List.ofFn fun e : Fin P'.m => if P'.cost e < 0 then 1 else 0) *
  Assn.list pCostPtrs costPtrs *
  Assn.list pCostLens (costLimbs.map List.length) *
  ∏ j ∈ Finset.range P'.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])

private theorem stage1Input_split_post (P' : Circulation) (k : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) :
    stage1Input P' k capPtrs capLimbs costPtrs costLimbs
        pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens =
      Assn.list pIn [P'.n, P'.m, k, pTail, pHead, pCapPtrs, pCapLens, pCostSign, pCostPtrs, pCostLens] *
      Assn.list pCapPtrs capPtrs *
      Assn.list pCapLens (capLimbs.map List.length) *
      (∏ j ∈ Finset.range P'.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
      stage1InputRest P' costPtrs costLimbs pTail pHead pCostSign pCostPtrs pCostLens := by
  unfold stage1Input stage1InputRest
  ac_rfl

private theorem stage1InputRest_noDebt (P' : Circulation) (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pTail pHead pCostSign pCostPtrs pCostLens : ℕ) :
    (stage1InputRest P' costPtrs costLimbs pTail pHead pCostSign pCostPtrs pCostLens).NoDebt := by
  unfold stage1InputRest
  exact (((((Assn.noDebt_list _ _).mul (Assn.noDebt_list _ _)).mul (Assn.noDebt_list _ _)).mul
    (Assn.noDebt_list _ _)).mul (Assn.noDebt_list _ _)).mul
    (Assn.noDebt_prod (Finset.range P'.m) fun j _ => Assn.noDebt_list _ _)

/-! ### `stage0FeasPostWrap`: read `m1, pCP1, pCL1`, run `feasPost`, store `ok` -/

wram_def stage0FeasPostWrap (feasPost : ℕ)
    (m1Orig, pIn1, pOut1, pOrigIdx1, pFeasFlow, L, pOkOut) {
  m1 := mem[pIn1 + 1]
  pCP1 := mem[pIn1 + 5]
  pCL1 := mem[pIn1 + 6]
  ok := feasPost(m1Orig, m1, pCP1, pCL1, pOrigIdx1, pOut1, pFeasFlow, L)
  mem[pOkOut] := ok
  return 0
}

structure Stage0FeasPostWrapData where
  I : Instance
  hv : I.IsValid
  hiso : FlowReduction.isolatedCheck I hv = true
  L : ℕ
  hLge : narrowMaxCapLimbs I + 1 ≤ L
  pShCapBuf : ℕ
  pShDemBuf : ℕ
  pOneCells : ℕ
  ok0 : ℕ
  f1 : Fin (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m → ℤ
  flowLimbs : Fin (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m → List ℕ

def stage0FeasPostWrapSpec (w : ℕ) : Spec Stage0FeasPostWrapData where
  pre := fun d args => ⨆ (pIn1 : ℕ) (pOut1 : ℕ) (pTail : ℕ) (pHead : ℕ)
      (pCapPtrs : ℕ) (pCapLens : ℕ) (pCostSign : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ)
      (pFlow : ℕ) (pOrigIdx1 : ℕ) (pFeasFlow : ℕ) (pOkOut : ℕ),
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    let orig := feasOrigPos d.I d.hv d.I.m
    let K1 := bitScalingPhases P' / k + 2
    ⌜args = [orig.length, pIn1, pOut1, pOrigIdx1, pFeasFlow, d.L, pOkOut] ∧
      1 ≤ d.L ∧ d.L < 2 ^ w ∧ 2 * k + 1 ≤ w ∧ 3 * d.I.m < 2 ^ w ∧
      (∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper) ∧
      (∀ e : Fin d.I.m, (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length ≤ d.L) ∧
      pIn1 + 10 ≤ 2 ^ w ∧ pOut1 + 2 ≤ 2 ^ w ∧ pOrigIdx1 + d.I.m ≤ 2 ^ w ∧
      pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      P'.m * K1 < 2 ^ w ∧ K1 < 2 ^ w ∧ K1 ≤ d.L + 2 ∧
      P'.Optimal (fun e => (d.f1 e : ℝ)) ∧
      (∀ e : Fin P'.m, 0 ≤ d.f1 e ∧ Limbs k (d.flowLimbs e) ∧ (d.flowLimbs e).length = K1 ∧
        ((Nat.ofDigits (2 ^ k) (d.flowLimbs e) : ℕ) : ℤ) = d.f1 e) ∧
      (∀ j : Fin P'.m, (Nat.digits (2 ^ k) (d.f1 j).toNat).length ≤ d.L) ∧
      (∀ j (hj : j < P'.m),
        CanonicalLimbs k ((feasCapLimbs d.I d.hv).getD j []) ∧
        Nat.ofDigits (2 ^ k) ((feasCapLimbs d.I d.hv).getD j []) = P'.capacity ⟨j, hj⟩)⌝ *
    stage1Input P' k (feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L) (feasCapLimbs d.I d.hv)
      (feasCostPtrs d.I d.hv d.pOneCells) (feasCostLimbs d.I d.hv)
      pIn1 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens *
    Assn.list pOut1 [pFlow, K1] *
    (∏ e ∈ Finset.range P'.m,
      Assn.list (pFlow + e * K1) (if h : e < P'.m then d.flowLimbs ⟨e, h⟩ else [])) *
    Assn.list pOrigIdx1 (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pFeasFlow + e * d.L) (List.replicate d.L 0)) *
    (pOkOut ↦ d.ok0)
  post := fun d args res => ⨆ (pIn1 : ℕ) (pOut1 : ℕ) (pOrigIdx1 : ℕ) (pFeasFlow : ℕ)
      (pOkOut : ℕ) (ok : ℕ) (f : Fin d.I.m → ℤ),
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    let orig := feasOrigPos d.I d.hv d.I.m
    ⌜args = [orig.length, pIn1, pOut1, pOrigIdx1, pFeasFlow, d.L, pOkOut] ∧
      res = 0 ∧ ok ≤ 1 ∧
      (ok = 1 →
        (∀ e : Fin d.I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ)) ∧
        d.I.IsFeasible (FlowReduction.restore d.I (fun e => (f e : ℝ)))) ∧
      (ok = 0 → ∀ x, ¬ d.I.IsFeasible x)⌝ *
    (∏ j ∈ Finset.range P'.m,
      Assn.list ((feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L).getD j 0)
        ((feasCapLimbs d.I d.hv).getD j [])) *
    (if ok = 1 then
      (∏ e ∈ Finset.range d.I.m,
        Assn.list (pFeasFlow + e * d.L)
          (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (f ⟨e, hlt⟩).toNat) d.L else []))
     else 1) *
    (pOkOut ↦ ok) * Assn.gc

/-! ### `stage0FeasRun`: Stage 1 → `feasPostWrap` -/

wram_def stage0FeasRun (stage1Circ feasPostWrap : ℕ)
    (m1Orig, pIn1, pOut1, pOrigIdx1, pFeasFlow, L, h, pOkOut) {
  h1 := stage1Circ(pIn1, pOut1, h)
  d := feasPostWrap(m1Orig, pIn1, pOut1, pOrigIdx1, pFeasFlow, L, pOkOut)
  return h1
}

structure Stage0FeasRunData where
  I : Instance
  hv : I.IsValid
  hiso : FlowReduction.isolatedCheck I hv = true
  L : ℕ
  hLge : narrowMaxCapLimbs I + 1 ≤ L
  pShCapBuf : ℕ
  pShDemBuf : ℕ
  pOneCells : ℕ
  ok0 : ℕ

def stage0FeasRunSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Stage0FeasRunData where
  pre := fun d args => ⨆ (pIn1 : ℕ) (pOut1 : ℕ) (pTail1 : ℕ) (pHead1 : ℕ)
      (pCapPtr1 : ℕ) (pCapLen1 : ℕ) (pCostSign1 : ℕ) (pCostPtr1 : ℕ) (pCostLen1 : ℕ)
      (pOrigIdx1 : ℕ) (pFeasFlow : ℕ) (h : ℕ) (pOkOut : ℕ),
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    let orig := feasOrigPos d.I d.hv d.I.m
    ⌜args = [orig.length, pIn1, pOut1, pOrigIdx1, pFeasFlow, d.L, h, pOkOut] ∧
      d.L < 2 ^ k ∧ 2 * k + 1 ≤ w ∧ 3 * d.I.m < 2 ^ w ∧
      (18 * d.I.m + 21) * upperClip (3 * d.I.m) < 2 ^ w ∧
      (∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper) ∧
      (∀ e : Fin d.I.m, (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length ≤ d.L) ∧
      pIn1 + 10 ≤ 2 ^ w ∧ pOut1 + 2 ≤ 2 ^ w ∧ pOrigIdx1 + d.I.m ≤ 2 ^ w ∧
      pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      d.I.n + 2 < 2 ^ w ∧ h + stage1CircSpace P' k S < 2 ^ w ∧
      (∀ j (hj : j < P'.m),
        CanonicalLimbs k ((feasCapLimbs d.I d.hv).getD j []) ∧
        ((feasCapLimbs d.I d.hv).getD j []).length * k < 2 ^ w ∧
        Nat.ofDigits (2 ^ k) ((feasCapLimbs d.I d.hv).getD j []) = P'.capacity ⟨j, hj⟩) ∧
      (∀ j (hj : j < P'.m),
        CanonicalLimbs k ((feasCostLimbs d.I d.hv).getD j []) ∧
        ((feasCostLimbs d.I d.hv).getD j []).length * k < 2 ^ w ∧
        Nat.ofDigits (2 ^ k) ((feasCostLimbs d.I d.hv).getD j []) = (P'.cost ⟨j, hj⟩).natAbs) ∧
      FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity < (2 ^ k) ^ d.L⌝ *
    stage1Input P' k (feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L) (feasCapLimbs d.I d.hv)
      (feasCostPtrs d.I d.hv d.pOneCells) (feasCostLimbs d.I d.hv)
      pIn1 pTail1 pHead1 pCapPtr1 pCapLen1 pCostSign1 pCostPtr1 pCostLen1 *
    Assn.list pOut1 (List.replicate 2 0) *
    Assn.list pOrigIdx1 (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pFeasFlow + e * d.L) (List.replicate d.L 0)) *
    (pOkOut ↦ d.ok0) * Assn.free h (2 ^ w - h)
  post := fun d args h' => ⨆ (pIn1 : ℕ) (pOut1 : ℕ) (pOrigIdx1 : ℕ) (pFeasFlow : ℕ)
      (h : ℕ) (pOkOut : ℕ) (ok : ℕ) (f : Fin d.I.m → ℤ),
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    let orig := feasOrigPos d.I d.hv d.I.m
    ⌜args = [orig.length, pIn1, pOut1, pOrigIdx1, pFeasFlow, d.L, h, pOkOut] ∧
      h ≤ h' ∧ h' ≤ h + stage1CircSpace P' k S ∧ ok ≤ 1 ∧
      (ok = 1 →
        (∀ e : Fin d.I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ)) ∧
        d.I.IsFeasible (FlowReduction.restore d.I (fun e => (f e : ℝ)))) ∧
      (ok = 0 → ∀ x, ¬ d.I.IsFeasible x)⌝ *
    (∏ j ∈ Finset.range P'.m,
      Assn.list ((feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L).getD j 0)
        ((feasCapLimbs d.I d.hv).getD j [])) *
    (if ok = 1 then
      (∏ e ∈ Finset.range d.I.m,
        Assn.list (pFeasFlow + e * d.L)
          (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (f ⟨e, hlt⟩).toNat) d.L else []))
     else 1) *
    (pOkOut ↦ ok) * Assn.free h' (2 ^ w - h') * Assn.gc

/-! ### `stage0FeasWork`: build → `feasRun` → restore `pShCapBuf * pShDemBuf` -/

wram_def stage0FeasWork (feasBuild feasRun : ℕ)
    (pEdges, pLabels, n, m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign, pShDemLen, L, k,
     pIn1, pOut1, pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1,
     pOrigIdx1, pOneCells, pFeasFlow, h, pOkOut) {
  m1Orig := feasBuild(pEdges, pLabels, n, m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign,
    pShDemLen, L, k, pIn1, pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1,
    pOrigIdx1, pOneCells)
  h1 := feasRun(m1Orig, pIn1, pOut1, pOrigIdx1, pFeasFlow, L, h, pOkOut)
  return h1
}

structure Stage0FeasWorkData where
  I : Instance
  hv : I.IsValid
  hiso : FlowReduction.isolatedCheck I hv = true
  act : List ℕ
  L : ℕ
  hLge : narrowMaxCapLimbs I + 1 ≤ L
  ok0 : ℕ

def stage0FeasWorkSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Stage0FeasWorkData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pLabels : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ)
      (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ) (pIn1 : ℕ) (pOut1 : ℕ)
      (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ)
      (pCostSign1 : ℕ) (pCostPtr1 : ℕ) (pCostLen1 : ℕ) (pOrigIdx1 : ℕ) (pOneCells : ℕ)
      (pFeasFlow : ℕ) (h : ℕ) (pOkOut : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    let cap := 3 * d.I.m
    ⌜args = [pEdges, pLabels, d.I.n, d.I.m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign,
        pShDemLen, d.L, k, pIn1, pOut1, pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1,
        pCostPtr1, pCostLen1, pOrigIdx1, pOneCells, pFeasFlow, h, pOkOut] ∧
      ActiveInv el d.act ∧ d.L < 2 ^ k ∧
      2 * k + 1 ≤ w ∧ (18 * d.I.m + 21) * upperClip (3 * d.I.m) < 2 ^ w ∧
      (∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pLabels + d.I.n ≤ 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pShCapLen + d.I.m ≤ 2 ^ w ∧
      pShDemBuf + el.count * d.L ≤ 2 ^ w ∧ el.count * d.L < 2 ^ w ∧
      pShDemSign + el.count ≤ 2 ^ w ∧ pShDemLen + el.count ≤ 2 ^ w ∧
      pIn1 + 10 ≤ 2 ^ w ∧ pOut1 + 2 ≤ 2 ^ w ∧
      pTail1 + cap ≤ 2 ^ w ∧ pHead1 + cap ≤ 2 ^ w ∧
      pCapPtr1 + cap ≤ 2 ^ w ∧ pCapLen1 + cap ≤ 2 ^ w ∧
      pCostSign1 + cap ≤ 2 ^ w ∧ pCostPtr1 + cap ≤ 2 ^ w ∧
      pCostLen1 + cap ≤ 2 ^ w ∧ pOrigIdx1 + d.I.m ≤ 2 ^ w ∧ pOneCells + cap ≤ 2 ^ w ∧
      pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧
      cap < 2 ^ w ∧ d.I.n + 2 < 2 ^ w ∧
      h + stage1CircSpace P' k S < 2 ^ w⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pShDemBuf + c * d.L)
        (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs) d.L)) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    Assn.list pIn1 (List.replicate 10 0) *
    Assn.list pOut1 (List.replicate 2 0) *
    Assn.list pTail1 (List.replicate cap 0) *
    Assn.list pHead1 (List.replicate cap 0) *
    Assn.list pCapPtr1 (List.replicate cap 0) *
    Assn.list pCapLen1 (List.replicate cap 0) *
    Assn.list pCostSign1 (List.replicate cap 0) *
    Assn.list pCostPtr1 (List.replicate cap 0) *
    Assn.list pCostLen1 (List.replicate cap 0) *
    Assn.list pOrigIdx1 (List.replicate d.I.m 0) *
    Assn.list pOneCells (List.replicate cap 0) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pFeasFlow + e * d.L) (List.replicate d.L 0)) *
    (pOkOut ↦ d.ok0) * Assn.free h (2 ^ w - h)
  post := fun d args h' => ⨆ (pEdges : ℕ) (pLabels : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ)
      (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ) (pIn1 : ℕ) (pOut1 : ℕ)
      (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ)
      (pCostSign1 : ℕ) (pCostPtr1 : ℕ) (pCostLen1 : ℕ) (pOrigIdx1 : ℕ) (pOneCells : ℕ)
      (pFeasFlow : ℕ) (h : ℕ) (pOkOut : ℕ) (ok : ℕ) (f : Fin d.I.m → ℤ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    ⌜args = [pEdges, pLabels, d.I.n, d.I.m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign,
        pShDemLen, d.L, k, pIn1, pOut1, pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1,
        pCostPtr1, pCostLen1, pOrigIdx1, pOneCells, pFeasFlow, h, pOkOut] ∧
      h ≤ h' ∧ h' ≤ h + stage1CircSpace P' k S ∧ ok ≤ 1 ∧
      (ok = 1 →
        (∀ e : Fin d.I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ)) ∧
        d.I.IsFeasible (FlowReduction.restore d.I (fun e => (f e : ℝ)))) ∧
      (ok = 0 → ∀ x, ¬ d.I.IsFeasible x)⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pShDemBuf + c * d.L)
        (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs) d.L)) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    (if ok = 1 then
      (∏ e ∈ Finset.range d.I.m,
        Assn.list (pFeasFlow + e * d.L)
          (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (f ⟨e, hlt⟩).toNat) d.L else []))
     else 1) *
    (pOkOut ↦ ok) * Assn.free h' (2 ^ w - h') * Assn.gc

private theorem feasWork_limb_bounds (d : Stage0FeasWorkData) {w : ℕ}
    (hact : ActiveInv (FlowReduction.shiftedGraph d.I d.hv).endpointLabels d.act)
    (hLlt : d.L < 2 ^ narrowLimbWidth d.I) (h2k1 : 2 * narrowLimbWidth d.I + 1 ≤ w) :
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    (∀ j (hj : j < P'.m),
      CanonicalLimbs k ((feasCapLimbs d.I d.hv).getD j []) ∧
      ((feasCapLimbs d.I d.hv).getD j []).length * k < 2 ^ w ∧
      Nat.ofDigits (2 ^ k) ((feasCapLimbs d.I d.hv).getD j []) = P'.capacity ⟨j, hj⟩) ∧
    (∀ j (hj : j < P'.m),
      CanonicalLimbs k ((feasCostLimbs d.I d.hv).getD j []) ∧
      ((feasCostLimbs d.I d.hv).getD j []).length * k < 2 ^ w ∧
      Nat.ofDigits (2 ^ k) ((feasCostLimbs d.I d.hv).getD j []) = (P'.cost ⟨j, hj⟩).natAbs) ∧
    (∀ e : Fin d.I.m,
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length ≤ d.L) ∧
    (∀ c < el.count,
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs).length ≤ d.L) ∧
    FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity < (2 ^ k) ^ d.L := by
  dsimp only
  have hLge : narrowMaxCapLimbs d.I + 1 ≤ d.L := d.hLge
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  set k := narrowLimbWidth d.I
  set P := FlowReduction.buildFeasibilityInstance d.I d.hv
  set P' := P.withoutZeroEdges
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth d.I
  have hb2k : 1 < 2 ^ k := by have := two_le_pow hk1; omega
  have hbud_lt : FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity < (2 ^ k) ^ d.L :=
    lt_of_lt_of_le (scalingCapacityBudget_lt_pow d.I d.hv)
      (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb2k) hLge)
  have hcap_le_bud : ∀ j : Fin P'.m, P'.capacity j ≤ FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity :=
    fun j => le_trans (Finset.le_sup (f := P'.capacity) (Finset.mem_univ j))
      (feasibility_withoutZeroEdges_maxCapacity_le d.I d.hv)
  have hcapLen_le : ∀ j (hj : j < P'.m), ((feasCapLimbs d.I d.hv).getD j []).length ≤ d.L := by
    intro j hj
    have hget : (feasCapLimbs d.I d.hv).getD j [] = Nat.digits (2 ^ k) (P'.capacity ⟨j, hj⟩) := by
      rw [List.getD_eq_getElem _ _ (by simp [feasCapLimbs]; exact hj)]
      simp [feasCapLimbs, Circulation.positiveIndex, P', P, k]
    rw [hget]
    exact digits_len_le_of_lt_pow hb2k (lt_of_le_of_lt (hcap_le_bud ⟨j, hj⟩) hbud_lt)
  have hkw : k < 2 ^ w :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (by omega : k ≤ w))
  refine ⟨feasCapLimbs_spec d.I d.hv hk3 h2k1 hLlt hcapLen_le,
    feasCostLimbs_spec d.I d.hv hk1 hkw, ?_, ?_, hbud_lt⟩
  · intro e
    have hle : (FlowReduction.shiftedGraph d.I d.hv).capacity e ≤
        FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity := by
      have h1 : (FlowReduction.shiftedGraph d.I d.hv).capacity e =
          P.capacity (Fin.castAdd (d.I.n + d.I.n) e) := by simp [P, Fin.addCases_left]
      rw [h1]
      exact FlowReduction.buildFeasibilityInstance_capacity_le d.I d.hv d.I.maxCapacity
        (demand_natAbs_le_maxCapacity' d.I d.hv) (lower_natAbs_le_maxCapacity' d.I)
        (upper_natAbs_le_maxCapacity' d.I) _
    exact digits_len_le_of_lt_pow hb2k (lt_of_le_of_lt hle hbud_lt)
  · intro c hc
    have hv_lt : d.act[c]'(by rw [hact.1]; exact hc) < d.I.n :=
      (hact.2 c (by rw [hact.1]; exact hc)).1
    let v : Fin d.I.n := ⟨d.act[c]'(by rw [hact.1]; exact hc), hv_lt⟩
    have hdem_eq : activeShiftedDemand d.I d.act c = FlowReduction.shiftedDemand d.I v := by
      unfold activeShiftedDemand
      rw [dite_eq_left (by rw [hact.1]; exact hc)]
      simp only [dite_eq_left hv_lt, v]
    rw [hdem_eq]
    have hle : (FlowReduction.shiftedDemand d.I v).natAbs ≤
        FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity := by
      by_cases hpos : 0 ≤ FlowReduction.shiftedDemand d.I v
      · have h1 : (FlowReduction.shiftedDemand d.I v).natAbs =
            P.capacity (Fin.natAdd d.I.m (Fin.castAdd d.I.n v)) := by
          simp only [P, Fin.addCases_right, Fin.addCases_left, FlowReduction.buildShiftedDemands_eq]
          omega
        rw [h1]
        exact FlowReduction.buildFeasibilityInstance_capacity_le d.I d.hv d.I.maxCapacity
          (demand_natAbs_le_maxCapacity' d.I d.hv) (lower_natAbs_le_maxCapacity' d.I)
          (upper_natAbs_le_maxCapacity' d.I) _
      · have h1 : (FlowReduction.shiftedDemand d.I v).natAbs =
            P.capacity (Fin.natAdd d.I.m (Fin.natAdd d.I.n v)) := by
          simp only [P, Fin.addCases_right, FlowReduction.buildShiftedDemands_eq]
          omega
        rw [h1]
        exact FlowReduction.buildFeasibilityInstance_capacity_le d.I d.hv d.I.maxCapacity
          (demand_natAbs_le_maxCapacity' d.I d.hv) (lower_natAbs_le_maxCapacity' d.I)
          (upper_natAbs_le_maxCapacity' d.I) _
    exact digits_len_le_of_lt_pow hb2k (lt_of_le_of_lt hle hbud_lt)

private theorem feasWork_flow_gc {m L k pFeasFlow ok : ℕ} (f_flow : Fin m → ℕ) :
    (∏ e ∈ Finset.range m,
      Assn.list (pFeasFlow + e * L)
        (if ok = 1 then
          (if hlt : e < m then padLimbs (Nat.digits (2 ^ k) (f_flow ⟨e, hlt⟩)) L else [])
         else List.replicate L 0)) ≤
    (if ok = 1 then
      (∏ e ∈ Finset.range m,
        Assn.list (pFeasFlow + e * L)
          (if hlt : e < m then padLimbs (Nat.digits (2 ^ k) (f_flow ⟨e, hlt⟩)) L else []))
     else 1) * Assn.gc := by
  by_cases hok_eq : ok = 1
  · rw [ite_eq_left hok_eq]
    have h1 : (∏ e ∈ Finset.range m,
        Assn.list (pFeasFlow + e * L)
          (if ok = 1 then
            (if hlt : e < m then padLimbs (Nat.digits (2 ^ k) (f_flow ⟨e, hlt⟩)) L else [])
           else List.replicate L 0)) =
        ∏ e ∈ Finset.range m,
          Assn.list (pFeasFlow + e * L)
            (if hlt : e < m then padLimbs (Nat.digits (2 ^ k) (f_flow ⟨e, hlt⟩)) L else []) :=
      Finset.prod_congr rfl fun _ _ => by rw [ite_eq_left hok_eq]
    rw [h1]
    have hle : (1 : Assn) ≤ Assn.gc := Assn.noDebt_one.le_gc
    simpa using mul_le_mul_right hle _
  · rw [ite_eq_right hok_eq, one_mul]
    have h1 : (∏ e ∈ Finset.range m,
        Assn.list (pFeasFlow + e * L)
          (if ok = 1 then
            (if hlt : e < m then padLimbs (Nat.digits (2 ^ k) (f_flow ⟨e, hlt⟩)) L else [])
           else List.replicate L 0)) =
        ∏ e ∈ Finset.range m, Assn.list (pFeasFlow + e * L) (List.replicate L 0) :=
      Finset.prod_congr rfl fun _ _ => by rw [ite_eq_right hok_eq]
    rw [h1]
    exact (Assn.noDebt_prod (Finset.range m) fun e _ =>
      Assn.noDebt_list (pFeasFlow + e * L) (List.replicate L 0)).le_gc

private theorem feasWork_stage1_arith (I : Instance) (hv : I.IsValid)
    (hiso : FlowReduction.isolatedCheck I hv = true) {L w h : ℕ} {S : ℕ → ℕ → ℕ}
    (hLge : narrowMaxCapLimbs I + 1 ≤ L)
    (hLlt : L < 2 ^ narrowLimbWidth I)
    (h2k1 : 2 * narrowLimbWidth I + 1 ≤ w)
    (hclip : (18 * I.m + 21) * upperClip (3 * I.m) < 2 ^ w)
    (hn2W : I.n + 2 < 2 ^ w)
    (hfit1 : h + stage1CircSpace (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
      (narrowLimbWidth I) S < 2 ^ w) :
    let k := narrowLimbWidth I
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    let K1 := bitScalingPhases P' / k + 2
    2 * P'.m + 1 < 2 ^ k ∧
    (6 * P'.m + 21) * upperClip P'.m < 2 ^ w ∧
    6 * P'.m + 4 < 2 ^ w ∧
    k + Nat.log 2 (2 * k) + 2 ≤ w ∧
    P'.n + 1 < 2 ^ w ∧
    K1 ≤ L + 2 ∧
    P'.m * K1 < 2 ^ w ∧
    K1 < 2 ^ w := by
  dsimp only
  set k := narrowLimbWidth I
  set P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
  set K1 := bitScalingPhases P' / k + 2
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth I
  have hm_le : P'.m ≤ 3 * I.m := feas_m_le_three_m I hv hiso
  have h2m1_lt : 2 * P'.m + 1 < 2 ^ k := by
    have h6m : 6 * I.m + 1 < 2 ^ k := six_mul_m_add_one_lt_pow_limbWidth I hv
    omega
  have hclip_P' : (6 * P'.m + 21) * upperClip P'.m < 2 ^ w := by
    have h1 : (6 * P'.m + 21) * upperClip P'.m ≤ (18 * I.m + 21) * upperClip (3 * I.m) :=
      Nat.mul_le_mul (by omega) (upperClip_mono hm_le)
    omega
  have h6m4_lt : 6 * P'.m + 4 < 2 ^ w := by
    have h1 := upperClip_pos P'.m
    have h2 : 6 * P'.m + 4 ≤ (6 * P'.m + 21) * upperClip P'.m :=
      calc 6 * P'.m + 4 ≤ (6 * P'.m + 21) * 1 := by omega
        _ ≤ (6 * P'.m + 21) * upperClip P'.m := Nat.mul_le_mul_left _ h1
    omega
  have hK1_le : K1 ≤ L + 2 := by
    have := stage1_Kcap_le_maxCapLimbs I hv P' (feasibility_withoutZeroEdges_maxCapacity_le I hv)
    dsimp only [K1, k]; omega
  have hFlow_lt : P'.m * K1 < 2 ^ w := by
    by_cases hm0 : P'.m = 0
    · rw [hm0, zero_mul]; exact Nat.pow_pos (by decide)
    · have hsp : 5 * P'.m * K1 ≤ stage1CircSpace P' k S := by
        unfold stage1CircSpace stage1StartSpace
        rw [ite_eq_right hm0]
        dsimp only [K1, k]
        omega
      have hle : P'.m * K1 ≤ 5 * P'.m * K1 := Nat.mul_le_mul_right K1 (by omega)
      omega
  have hK1W : K1 < 2 ^ w := by
    have h2k_le : 2 ^ k + 2 ≤ 2 ^ w := by
      have h1 : 2 ^ (k + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
      have h3 : 8 ≤ 2 ^ k := by
        calc 8 = 2 ^ 3 := by decide
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk3
      omega
    omega
  exact ⟨h2m1_lt, hclip_P', h6m4_lt, stage1_k_log_bound hk3 h2k1,
    by omega, hK1_le, hFlow_lt, hK1W⟩

theorem stage0FeasPostWrap_meets {w : ℕ} {p : Program} {f feasPost : ℕ}
    {Tp : ℕ → ℕ → ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0FeasPostWrap feasPost))
    (hpo : Meets w p feasPost ((stage0FeasPostSpec w).withCost fun d _ =>
      let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
      let orig := feasOrigPos d.I d.hv d.I.m
      let K1 := bitScalingPhases P' / narrowLimbWidth d.I + 2
      Tp K1 d.L (P'.m - orig.length) orig.length)) :
    Meets w p f ((stage0FeasPostWrapSpec w).withCost fun d _ =>
      let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
      let orig := feasOrigPos d.I d.hv d.I.m
      let K1 := bitScalingPhases P' / narrowLimbWidth d.I + 2
      Tp K1 d.L (P'.m - orig.length) orig.length + 50) := by
  sep_enter d with hL1 hLW h2k1 hcapW hcaps hshCapLen hpIn hpOut hpOI hpFF hmL hFlow_lt hK1W hK1_le hopt_P' hfl_P' hdig_fl hcanPost
  set k := narrowLimbWidth d.I
  set P := FlowReduction.buildFeasibilityInstance d.I d.hv
  set P' := P.withoutZeroEdges
  set K1 := bitScalingPhases P' / k + 2
  have hcpLen : (feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L).length = P'.m := by
    simp only [feasCapPtrs, List.length_map]; rfl
  have hclLen : ((feasCapLimbs d.I d.hv).map List.length).length = P'.m := by
    simp only [List.length_map, feasCapLimbs]; rfl
  sep_apply stage1Input_split_post P' k
    (feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L) (feasCapLimbs d.I d.hv)
    (feasCostPtrs d.I d.hv d.pOneCells) (feasCostLimbs d.I d.hv)
    pIn1 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens
  sep_step; sep_step; sep_step
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hm1 hpCP1 hpCL1
  subst m1 pCP1 pCL1
  generalize hF4 :
    ((pOkOut ↦ d.ok0) *
     Assn.list pIn1 [P'.n, P'.m, k, pTail, pHead, pCapPtrs, pCapLens, pCostSign, pCostPtrs, pCostLens] *
     stage1InputRest P' (feasCostPtrs d.I d.hv d.pOneCells) (feasCostLimbs d.I d.hv)
       pTail pHead pCostSign pCostPtrs pCostLens) = F4
  sep_apply hF4
  sep_step from (⟨d.I, d.hv, d.hiso, d.L, d.pShCapBuf, d.pShDemBuf, d.f1, d.flowLimbs⟩ : FeasPostData)
    with hok_le hok1 hok0
  · subst F4; sep_norm
    sep_apply (stage1InputRest_noDebt P' (feasCostPtrs d.I d.hv d.pOneCells) (feasCostLimbs d.I d.hv)
      pTail pHead pCostSign pCostPtrs pCostLens).le_gc
    sep_step
    sep_apply feasWork_flow_gc (pFeasFlow := pFeasFlow) (L := d.L) (k := k) (ok := ok)
      (fun e : Fin d.I.m => (P.scatterPositive d.f1 (Fin.castAdd (d.I.n + d.I.n) e)).toNat)
    generalize hf_res : (fun e : Fin d.I.m => P.scatterPositive d.f1 (Fin.castAdd (d.I.n + d.I.n) e)) = f_res
    have hfl_rw : (if ok = 1 then
          ∏ e ∈ Finset.range d.I.m,
            Assn.list (pFeasFlow + e * d.L)
              (if hlt : e < d.I.m then
                padLimbs (Nat.digits (2 ^ k) (P.scatterPositive d.f1 (Fin.castAdd (d.I.n + d.I.n) ⟨e, hlt⟩)).toNat) d.L
              else [])
        else 1) =
        (if ok = 1 then
          ∏ e ∈ Finset.range d.I.m,
            Assn.list (pFeasFlow + e * d.L)
              (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (f_res ⟨e, hlt⟩).toNat) d.L else [])
        else 1) := by
      rw [← hf_res]
    sep_apply hfl_rw
    have hf_eq : ∀ e : Fin d.I.m, f_res e = P.scatterPositive d.f1 (Fin.castAdd (d.I.n + d.I.n) e) :=
      fun e => (congrFun hf_res e).symm
    have hok1' : ok = 1 →
        (∀ e : Fin d.I.m, 0 ≤ f_res e ∧ f_res e ≤ ((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ)) ∧
        d.I.IsFeasible (FlowReduction.restore d.I (fun e => (f_res e : ℝ))) := by
      intro h1; simpa only [hf_eq] using hok1 h1
    sep_step
    · dsimp only [K1, P', P, k]; omega
  · by_cases hm0 : P'.m = 0
    · change pCapPtrs + P'.m ≤ 2 ^ w; rw [hm0, add_zero]; omega
    · change pCapPtrs + P'.m ≤ 2 ^ w; omega
  · by_cases hm0 : P'.m = 0
    · change pCapLens + P'.m ≤ 2 ^ w; rw [hm0, add_zero]; omega
    · change pCapLens + P'.m ≤ 2 ^ w; omega

theorem stage0FeasRun_meets {w : ℕ} {p : Program} {S : ℕ → ℕ → ℕ}
    {f stage1Circ feasPostWrap : ℕ}
    {T1 : Circulation → ℕ} {Tp : ℕ → ℕ → ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0FeasRun stage1Circ feasPostWrap))
    (hs1 : Meets w p stage1Circ ((stage1CircSpec w S).withCost fun x _ => T1 x.1))
    (hpw : Meets w p feasPostWrap ((stage0FeasPostWrapSpec w).withCost fun d _ =>
      let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
      let orig := feasOrigPos d.I d.hv d.I.m
      let K1 := bitScalingPhases P' / narrowLimbWidth d.I + 2
      Tp K1 d.L (P'.m - orig.length) orig.length)) :
    Meets w p f ((stage0FeasRunSpec w S).withCost fun d _ =>
      let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
      let orig := feasOrigPos d.I d.hv d.I.m
      let K1 := bitScalingPhases P' / narrowLimbWidth d.I + 2
      T1 P' + Tp K1 d.L (P'.m - orig.length) orig.length + 90) := by
  sep_enter d with hLlt h2k1 hcapW hclip hcaps hshCapLen hpIn hpOut hpOI hpFF hmL hn2W hfit1 hcapSpec hcostSpec hbud_lt
  set k := narrowLimbWidth d.I
  set P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have hb2k : 1 < 2 ^ k := by have := two_le_pow hk1; omega
  have hLge : narrowMaxCapLimbs d.I + 1 ≤ d.L := d.hLge
  have hL1 : 1 ≤ d.L := by omega
  have hLW : d.L < 2 ^ w :=
    lt_of_lt_of_le hLlt (Nat.pow_le_pow_right (by decide) (by omega : k ≤ w))
  have hcap_le_bud : ∀ j : Fin P'.m, P'.capacity j ≤ FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity :=
    fun j => le_trans (Finset.le_sup (f := P'.capacity) (Finset.mem_univ j))
      (feasibility_withoutZeroEdges_maxCapacity_le d.I d.hv)
  obtain ⟨h2m1_lt, hclip_P', h6m4_lt, hklg, hPn1W, hK1_le, hFlow_lt, hK1W⟩ :=
    feasWork_stage1_arith d.I d.hv d.hiso d.hLge hLlt h2k1 hclip hn2W hfit1
  have hcpLen : (feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L).length = P'.m := by
    simp only [feasCapPtrs, List.length_map]; rfl
  have hclLen : (feasCapLimbs d.I d.hv).length = P'.m := by
    simp only [feasCapLimbs, List.length_map]; rfl
  have hcopLen : (feasCostPtrs d.I d.hv d.pOneCells).length = P'.m := by
    dsimp only [feasCostPtrs]; rw [List.length_ofFn]
  have hcolLen : (feasCostLimbs d.I d.hv).length = P'.m := by
    dsimp only [feasCostLimbs]; rw [List.length_ofFn]
  sep_step from (P', k, feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L, feasCapLimbs d.I d.hv,
      feasCostPtrs d.I d.hv d.pOneCells, feasCostLimbs d.I d.hv, List.replicate 2 0)
    with hh1_lo hh1_hi hopt_P' hfl_P'
  have hdig_fl : ∀ j : Fin P'.m, (Nat.digits (2 ^ k) (f_1 j).toNat).length ≤ d.L := by
    intro j
    have hfj_le : (f_1 j).toNat ≤ P'.capacity j := by
      have h1 : (f_1 j : ℝ) ≤ (P'.capacity j : ℝ) := (hopt_P'.1.2 j).2
      have h2 : f_1 j ≤ (P'.capacity j : ℤ) := by exact_mod_cast h1
      have h3 := (hfl_P' j).1
      omega
    exact digits_len_le_of_lt_pow hb2k (lt_of_le_of_lt (le_trans hfj_le (hcap_le_bud j)) hbud_lt)
  have hcanPost : ∀ j (hj : j < P'.m),
      CanonicalLimbs k ((feasCapLimbs d.I d.hv).getD j []) ∧
      Nat.ofDigits (2 ^ k) ((feasCapLimbs d.I d.hv).getD j []) = P'.capacity ⟨j, hj⟩ :=
    fun j hj => ⟨(hcapSpec j hj).1, (hcapSpec j hj).2.2⟩
  sep_step from (⟨d.I, d.hv, d.hiso, d.L, d.hLge, d.pShCapBuf, d.pShDemBuf, d.pOneCells,
      d.ok0, f_1, flowLimbs⟩ : Stage0FeasPostWrapData)
    with hok_le hok1 hok0
  sep_step
  · dsimp only [P', k]; omega

theorem stage0FeasWork_meets {w : ℕ} {p : Program} {S : ℕ → ℕ → ℕ}
    {f feasBuild feasRun : ℕ}
    {Tb : ℕ → ℕ → ℕ} {Tr : Stage0FeasRunData → ℕ}
    (hp : p.procs[f]? = some (stage0FeasWork feasBuild feasRun))
    (hb : Meets w p feasBuild ((stage0FeasBuildSpec w).withCost fun d _ => Tb d.I.m d.I.n))
    (hr : Meets w p feasRun ((stage0FeasRunSpec w S).withCost fun d _ => Tr d))
    (hTr_indep : ∀ d₁ d₂ : Stage0FeasRunData, d₁.I = d₂.I → d₁.L = d₂.L → Tr d₁ = Tr d₂) :
    Meets w p f ((stage0FeasWorkSpec w S).withCost fun d _ =>
      Tb d.I.m d.I.n + Tr ⟨d.I, d.hv, d.hiso, d.L, d.hLge, 0, 0, 0, 0⟩ + 50) := by
  sep_enter d with hact hLlt h2k1 hclip hcaps hpE h11m hpLab hpCap hmL hpLen
    hpDem hcntL hpS hpL hpIn hpOut hpT hpH hpCP hpCL hpCS hpCoP hpCoL hpOI hpOne
    hpFF hcapW hn2W hfit1
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  set k := narrowLimbWidth d.I
  set P := FlowReduction.buildFeasibilityInstance d.I d.hv
  set P' := P.withoutZeroEdges
  set orig := feasOrigPos d.I d.hv d.I.m
  have hLge : narrowMaxCapLimbs d.I + 1 ≤ d.L := d.hLge
  have hL1 : 1 ≤ d.L := by omega
  have hLW : d.L < 2 ^ w :=
    lt_of_lt_of_le hLlt (Nat.pow_le_pow_right (by decide) (by omega : k ≤ w))
  obtain ⟨hcapSpec, hcostSpec, hshCapLen, hshDemLen, hbud_lt⟩ :=
    feasWork_limb_bounds d hact hLlt h2k1
  generalize hF1 :
    ((∏ i ∈ Finset.range d.I.m,
        Assn.list (pShCapBuf + i * d.L)
          (if hlt : i < d.I.m then
            padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
          else [])) *
     (∏ c ∈ Finset.range el.count,
        Assn.list (pShDemBuf + c * d.L)
          (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs) d.L)) *
     Assn.list pOut1 (List.replicate 2 0) *
     (∏ e ∈ Finset.range d.I.m, Assn.list (pFeasFlow + e * d.L) (List.replicate d.L 0)) *
     (pOkOut ↦ d.ok0) * Assn.free h (2 ^ w - h)) = F1
  sep_apply hF1
  sep_step from (⟨d.I, d.hv, d.hiso, d.act, d.L⟩ : Stage0FeasBuildData)
  generalize hF2 :
    ((∏ i ∈ Finset.range d.I.m,
        Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
     Assn.list pLabels (List.ofFn el.table) *
     Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
       (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
     Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
       if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
     Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
       (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length)) = F2
  sep_apply hF2
  subst F1; sep_norm
  obtain ⟨R_cap, hcap_split0⟩ :=
    feas_split_shCap_shDem d.I d.hv d.hiso hact pShCapBuf pShDemBuf d.L hshCapLen hshDemLen
  have hcap_split :
      (∏ i ∈ Finset.range d.I.m,
        Assn.list (pShCapBuf + i * d.L)
          (if hlt : i < d.I.m then
            padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
          else [])) *
      (∏ c ∈ Finset.range el.count,
        Assn.list (pShDemBuf + c * d.L)
          (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs) d.L)) =
      (∏ j ∈ Finset.range P'.m,
        Assn.list ((feasCapPtrs d.I d.hv pShCapBuf pShDemBuf d.L).getD j 0)
          ((feasCapLimbs d.I d.hv).getD j [])) * holdAssn R_cap := hcap_split0
  sep_apply hcap_split
  have hfold_in :
      Assn.list pIn1 [P'.n, P'.m, k, pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1] *
      Assn.list pTail1 (List.ofFn fun e : Fin P'.m => (P'.tail e).val) *
      Assn.list pHead1 (List.ofFn fun e : Fin P'.m => (P'.head e).val) *
      Assn.list pCapPtr1 (feasCapPtrs d.I d.hv pShCapBuf pShDemBuf d.L) *
      Assn.list pCapLen1 ((feasCapLimbs d.I d.hv).map List.length) *
      (∏ j ∈ Finset.range P'.m,
        Assn.list ((feasCapPtrs d.I d.hv pShCapBuf pShDemBuf d.L).getD j 0)
          ((feasCapLimbs d.I d.hv).getD j [])) *
      Assn.list pCostSign1 (List.ofFn fun e : Fin P'.m => if P'.cost e < 0 then 1 else 0) *
      Assn.list pCostPtr1 (feasCostPtrs d.I d.hv pOneCells) *
      Assn.list pCostLen1 ((feasCostLimbs d.I d.hv).map List.length) *
      (∏ j ∈ Finset.range P'.m,
        Assn.list ((feasCostPtrs d.I d.hv pOneCells).getD j 0)
          ((feasCostLimbs d.I d.hv).getD j [])) =
      stage1Input P' k (feasCapPtrs d.I d.hv pShCapBuf pShDemBuf d.L) (feasCapLimbs d.I d.hv)
        (feasCostPtrs d.I d.hv pOneCells) (feasCostLimbs d.I d.hv)
        pIn1 pTail1 pHead1 pCapPtr1 pCapLen1 pCostSign1 pCostPtr1 pCostLen1 := by
    unfold stage1Input; ac_rfl
  sep_apply hfold_in
  have hTr_eq : Tr ⟨d.I, d.hv, d.hiso, d.L, d.hLge, pShCapBuf, pShDemBuf, pOneCells, d.ok0⟩ =
      Tr ⟨d.I, d.hv, d.hiso, d.L, d.hLge, 0, 0, 0, 0⟩ :=
    hTr_indep _ _ rfl rfl
  sep_step from (⟨d.I, d.hv, d.hiso, d.L, d.hLge, pShCapBuf, pShDemBuf, pOneCells, d.ok0⟩ : Stage0FeasRunData)
    with hh1_lo hh1_hi hok_le hok1 hok0
  subst F2; sep_norm
  sep_apply hcap_split.symm
  sep_step

end MinCostFlow.NarrowProg
