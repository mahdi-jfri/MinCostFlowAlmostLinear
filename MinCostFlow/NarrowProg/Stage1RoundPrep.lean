module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.BitScale
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1Layout
public import MinCostFlow.NarrowProg.Stage1RoundedCosts
public import MinCostFlow.NarrowProg.Stage1ResCaps
public import MinCostFlow.NarrowProg.Stage1Dual
public import MinCostFlow.NarrowProg.Stage1FlowUpdate
public import MinCostFlow.NarrowProg.Stage1StateUpdate
import MinCostFlow.Narrow.CostUnitsClip
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Per-step dispatch helpers for one Stage 1 round (Part 5b-1)

Six small wrapper procedures that unpack the needed pointers from the Stage 1
context header (`lay.pCtx`, `lay.pResIn`, `lay.pResOut`) and invoke each
stage of one cost-scaling round:
1. `stage1RoundCostsCall`: calls `stage1RoundedCosts`
2. `stage1RoundResCapsCall`: calls `stage1ResCaps`
3. `stage1RoundBitScaleCall`: calls Stage 2 `bitScale` (`bitScaleSpec`)
4. `stage1RoundDualCall`: calls `stage1DualExtract`
5. `stage1RoundFlowCall`: calls `stage1FlowUpdate`
6. `stage1RoundStateCall`: calls `stage1StateUpdate`
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate List.length_append List.length_map

/-! ### Shared context-header bundle (`s1CtxHdr`) and 3-chunk split -/

/-- Persistent Stage 1 context + residual input descriptor headers. -/
def s1CtxHdr (I : Circulation) (k : ℕ) (lay : Stage1Layout) (pCostSign pCostLens : ℕ) : Assn :=
  Assn.list lay.pCtx (stage1CtxWords I k lay pCostSign pCostLens) *
  Assn.list lay.pResIn
    [I.compress.n, 2 * I.m, k, lay.pResTail, lay.pResHead, lay.pResCSign, lay.pResCMag,
     lay.pResCapPtrs, lay.pResCapLens]

/-- Split `lay.pCtx` (24 words) into three 8-word chunks so every `mem[pCtx + i]` load
indexes into an 8-element list literal. -/
theorem s1CtxHdr_split (I : Circulation) (k : ℕ) (lay : Stage1Layout) (pCostSign pCostLens : ℕ) :
    s1CtxHdr I k lay pCostSign pCostLens =
      Assn.list lay.pCtx
        [I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I,
         bitScalingPhases I / k + 2, lowerClip I.m, upperClip I.m] *
      Assn.list (lay.pCtx + 8)
        [freezeThreshold I.m, narrowCostRounds I.compress, lay.pCompTail, lay.pCompHead,
         pCostSign, pCostLens, lay.pAdjCostPtrs, lay.pCapBuf] *
      Assn.list (lay.pCtx + 16)
        [lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
         lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn] *
      Assn.list lay.pResIn
        [I.compress.n, 2 * I.m, k, lay.pResTail, lay.pResHead, lay.pResCSign, lay.pResCMag,
         lay.pResCapPtrs, lay.pResCapLens] := by
  unfold s1CtxHdr stage1CtxWords
  have h1 : Assn.list lay.pCtx
      ([I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I,
        bitScalingPhases I / k + 2, lowerClip I.m, upperClip I.m] ++
       ([freezeThreshold I.m, narrowCostRounds I.compress, lay.pCompTail, lay.pCompHead,
         pCostSign, pCostLens, lay.pAdjCostPtrs, lay.pCapBuf] ++
        [lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
         lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn])) =
      Assn.list lay.pCtx
        [I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I,
         bitScalingPhases I / k + 2, lowerClip I.m, upperClip I.m] *
      Assn.list (lay.pCtx + 8)
        [freezeThreshold I.m, narrowCostRounds I.compress, lay.pCompTail, lay.pCompHead,
         pCostSign, pCostLens, lay.pAdjCostPtrs, lay.pCapBuf] *
      Assn.list (lay.pCtx + 16)
        [lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
         lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn] := by
    rw [Assn.list_append, Assn.list_append]
    simp [Nat.add_assoc, mul_assoc]
  have h1' : Assn.list lay.pCtx
      [I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I,
       bitScalingPhases I / k + 2, lowerClip I.m, upperClip I.m,
       freezeThreshold I.m, narrowCostRounds I.compress, lay.pCompTail, lay.pCompHead,
       pCostSign, pCostLens, lay.pAdjCostPtrs, lay.pCapBuf,
       lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
       lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn] =
      Assn.list lay.pCtx
        [I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I,
         bitScalingPhases I / k + 2, lowerClip I.m, upperClip I.m] *
      Assn.list (lay.pCtx + 8)
        [freezeThreshold I.m, narrowCostRounds I.compress, lay.pCompTail, lay.pCompHead,
         pCostSign, pCostLens, lay.pAdjCostPtrs, lay.pCapBuf] *
      Assn.list (lay.pCtx + 16)
        [lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
         lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn] := h1
  rw [h1']

/-! ### Helper arithmetic lemmas for residual instances -/

theorem narrowRound_tail_list (C : Circulation) (s : NarrowCostState C) :
    (List.ofFn fun a : Fin (narrowRoundInstance C s).m => ((narrowRoundInstance C s).tail a).val) =
      (List.ofFn fun e : Fin C.m => (C.tail e).val) ++
      (List.ofFn fun e : Fin C.m => (C.head e).val) := by
  refine List.ext_getElem (by simp [narrowRoundInstance, Circulation.residual]) fun i hi1 hi2 => ?_
  by_cases h : i < C.m
  · rw [List.getElem_ofFn, List.getElem_append_left (by simp [h]), List.getElem_ofFn]
    have hfin : (⟨i, by simpa using hi1⟩ : Fin (C.m + C.m)) = Fin.castAdd C.m ⟨i, h⟩ := by ext; rfl
    change ((C.residual s.flow).tail ⟨i, by simpa using hi1⟩).val = _
    rw [hfin]; simp only [Circulation.residual, Fin.addCases_left]
  · rw [List.getElem_ofFn, List.getElem_append_right (by simp; omega), List.getElem_ofFn]
    have hi' : i - C.m < C.m := by simp [narrowRoundInstance, Circulation.residual] at hi1; omega
    have hfin : (⟨i, by simpa using hi1⟩ : Fin (C.m + C.m)) = Fin.natAdd C.m ⟨i - C.m, hi'⟩ := by
      ext; simp [Fin.natAdd]; omega
    change ((C.residual s.flow).tail ⟨i, by simpa using hi1⟩).val = _
    rw [hfin]; simp only [Circulation.residual, Fin.addCases_right, List.length_ofFn]

theorem narrowRound_head_list (C : Circulation) (s : NarrowCostState C) :
    (List.ofFn fun a : Fin (narrowRoundInstance C s).m => ((narrowRoundInstance C s).head a).val) =
      (List.ofFn fun e : Fin C.m => (C.head e).val) ++
      (List.ofFn fun e : Fin C.m => (C.tail e).val) := by
  refine List.ext_getElem (by simp [narrowRoundInstance, Circulation.residual]) fun i hi1 hi2 => ?_
  by_cases h : i < C.m
  · rw [List.getElem_ofFn, List.getElem_append_left (by simp [h]), List.getElem_ofFn]
    have hfin : (⟨i, by simpa using hi1⟩ : Fin (C.m + C.m)) = Fin.castAdd C.m ⟨i, h⟩ := by ext; rfl
    change ((C.residual s.flow).head ⟨i, by simpa using hi1⟩).val = _
    rw [hfin]; simp only [Circulation.residual, Fin.addCases_left]
  · rw [List.getElem_ofFn, List.getElem_append_right (by simp; omega), List.getElem_ofFn]
    have hi' : i - C.m < C.m := by simp [narrowRoundInstance, Circulation.residual] at hi1; omega
    have hfin : (⟨i, by simpa using hi1⟩ : Fin (C.m + C.m)) = Fin.natAdd C.m ⟨i - C.m, hi'⟩ := by
      ext; simp [Fin.natAdd]; omega
    change ((C.residual s.flow).head ⟨i, by simpa using hi1⟩).val = _
    rw [hfin]; simp only [Circulation.residual, Fin.addCases_right, List.length_ofFn]

theorem bitScalingPhases_narrowRound_le (C : Circulation) (s : NarrowCostState C)
    (hf : ∀ e, 0 ≤ s.flow e ∧ s.flow e ≤ (C.capacity e : ℤ)) :
    bitScalingPhases (narrowRoundInstance C s) ≤ bitScalingPhases C :=
  Nat.size_le_size (circMaxCapacity_narrowRound_le C s hf)

theorem bitScaleSpace_narrowRound_le (C : Circulation) (s : NarrowCostState C) (k : ℕ)
    (S : ℕ → ℕ → ℕ) (hf : ∀ e, 0 ≤ s.flow e ∧ s.flow e ≤ (C.capacity e : ℤ)) :
    bitScaleSpace (narrowRoundInstance C s) k S ≤ stage1RoundBitScaleSpace C k S := by
  have hT := bitScalingPhases_narrowRound_le C s hf
  have hdiv : bitScalingPhases (narrowRoundInstance C s) / k ≤ bitScalingPhases C / k :=
    Nat.div_le_div_right hT
  unfold bitScaleSpace stage1RoundBitScaleSpace
  change 5 + 2 * (C.m + C.m) + 3 * (C.m + C.m) * (bitScalingPhases (narrowRoundInstance C s) / k + 2) +
      bitScalingPhases (narrowRoundInstance C s) * (2 + 12 * (C.m + C.m) + S (C.n + 1) (2 * (C.m + C.m))) ≤
    5 + 4 * C.m + 6 * C.m * (bitScalingPhases C / k + 2) +
      bitScalingPhases C * (2 + 24 * C.m + S (C.n + 1) (4 * C.m))
  have h1 : 2 * (C.m + C.m) = 4 * C.m := by omega
  have h2 : 3 * (C.m + C.m) = 6 * C.m := by omega
  have h3 : 12 * (C.m + C.m) = 24 * C.m := by omega
  rw [h1, h2, h3]
  have hm1 := Nat.mul_le_mul_left (6 * C.m) (Nat.add_le_add_right hdiv 2)
  have hm2 := Nat.mul_le_mul_right (2 + 24 * C.m + S (C.n + 1) (4 * C.m)) hT
  omega

theorem stage1DualExtractSpace_narrowRound (C : Circulation) (s : NarrowCostState C)
    (S : ℕ → ℕ → ℕ) :
    stage1DualExtractSpace (narrowRoundInstance C s) S = stage1DualSpace C S := by
  unfold stage1DualExtractSpace stage1DualSpace
  change let Sm := 2 * (C.m + C.m) + C.n; _ = _
  have h : 2 * (C.m + C.m) + C.n = 4 * C.m + C.n := by omega
  simp only [h]

/-! ### 1. `stage1RoundCostsCall` -/

/-- Load pointers from `pCtx` and `pResIn` and invoke `stage1RoundedCosts`. -/
wram_def stage1RoundCostsCall (rcIdx : ℕ) (pCtx) {
  m := mem[pCtx + 1]
  lo := mem[pCtx + 6]
  up := mem[pCtx + 7]
  pFrozen := mem[pCtx + 20]
  pHSign := mem[pCtx + 21]
  pHMag := mem[pCtx + 22]
  pResIn := mem[pCtx + 23]
  pResCSign := mem[pResIn + 5]
  pResCMag := mem[pResIn + 6]
  r := rcIdx(m, pFrozen, pHSign, pHMag, lo, up, pResCSign, pResCMag)
  return 0
}

structure S1RoundCostsArg where
  I : Circulation
  k : ℕ
  lay : Stage1Layout
  pCostSign : ℕ
  pCostLens : ℕ
  s : NarrowCostState I.compress
  oldSign : List ℕ
  oldMag : List ℕ

def stage1RoundCostsCallSpec (w : ℕ) : Spec S1RoundCostsArg where
  pre := fun g args =>
    let C := g.I.compress
    ⌜args = [g.lay.pCtx] ∧
      g.oldSign.length = 2 * g.I.m ∧ g.oldMag.length = 2 * g.I.m ∧
      (∀ e : Fin C.m, (g.s.halfCost e).natAbs + 1 < 2 ^ w) ∧
      2 < 2 ^ w ∧ upperClip g.I.m < 2 ^ w⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    Assn.list g.lay.pFrozen (List.ofFn fun e : Fin g.I.m => freezeCode (g.s.frozen e)) *
    Assn.list g.lay.pHSign (List.ofFn fun e : Fin g.I.m => if g.s.halfCost e < 0 then 1 else 0) *
    Assn.list g.lay.pHMag (List.ofFn fun e : Fin g.I.m => (g.s.halfCost e).natAbs) *
    Assn.list g.lay.pResCSign g.oldSign *
    Assn.list g.lay.pResCMag g.oldMag
  post := fun g args v =>
    let C := g.I.compress
    ⌜args = [g.lay.pCtx] ∧ v = 0⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    Assn.list g.lay.pFrozen (List.ofFn fun e : Fin g.I.m => freezeCode (g.s.frozen e)) *
    Assn.list g.lay.pHSign (List.ofFn fun e : Fin g.I.m => if g.s.halfCost e < 0 then 1 else 0) *
    Assn.list g.lay.pHMag (List.ofFn fun e : Fin g.I.m => (g.s.halfCost e).natAbs) *
    Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
      if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
    Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
      (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs)

private def s1RCBody (g : S1RoundCostsArg) : Assn :=
  Assn.list g.lay.pFrozen (List.ofFn fun e : Fin g.I.m => freezeCode (g.s.frozen e)) *
  Assn.list g.lay.pHSign (List.ofFn fun e : Fin g.I.m => if g.s.halfCost e < 0 then 1 else 0) *
  Assn.list g.lay.pHMag (List.ofFn fun e : Fin g.I.m => (g.s.halfCost e).natAbs) *
  Assn.list g.lay.pResCSign g.oldSign *
  Assn.list g.lay.pResCMag g.oldMag

private theorem s1RCBody_eq (g : S1RoundCostsArg) :
    Assn.list g.lay.pFrozen (List.ofFn fun e : Fin g.I.m => freezeCode (g.s.frozen e)) *
    Assn.list g.lay.pHSign (List.ofFn fun e : Fin g.I.m => if g.s.halfCost e < 0 then 1 else 0) *
    Assn.list g.lay.pHMag (List.ofFn fun e : Fin g.I.m => (g.s.halfCost e).natAbs) *
    Assn.list g.lay.pResCSign g.oldSign *
    Assn.list g.lay.pResCMag g.oldMag = s1RCBody g := rfl

theorem stage1RoundCostsCall_meets {w : ℕ} {p : Program} {f rcIdx : ℕ}
    (hp : p.procs[f]? = some (stage1RoundCostsCall rcIdx))
    (hrc : Meets w p rcIdx ((stage1RoundedCostsSpec w).withCost fun inp _ => 170 * inp.C.m + 30)) :
    Meets w p f ((stage1RoundCostsCallSpec w).withCost fun g _ => 170 * g.I.m + 120) := by
  sep_enter g with hos hom hx hw2 hup
  sep_apply s1RCBody_eq g
  sep_apply s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens
  iterate 7 sep_step
  subst m lo up pFrozen pHSign pHMag pResIn
  iterate 2 sep_step
  subst pResCSign pResCMag
  sep_apply (s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens).symm
  sep_apply (s1RCBody_eq g).symm
  sep_step from ⟨g.I.compress, g.s.frozen, g.s.halfCost, g.oldSign, g.oldMag⟩
  sep_run

/-! ### 2. `stage1RoundResCapsCall` -/

/-- Load pointers from `pCtx` and `pResIn` and invoke `stage1ResCaps`. -/
wram_def stage1RoundResCapsCall (resCapsIdx : ℕ) (pCtx) {
  m := mem[pCtx + 1]
  k := mem[pCtx + 2]
  Kcap := mem[pCtx + 5]
  pCapBuf := mem[pCtx + 15]
  pFlow := mem[pCtx + 16]
  pResFwdBuf := mem[pCtx + 17]
  pResIn := mem[pCtx + 23]
  pResCapLens := mem[pResIn + 8]
  r := resCapsIdx(m, k, Kcap, pCapBuf, pFlow, pResFwdBuf, pResCapLens)
  return 0
}

structure S1RoundResCapsArg where
  I : Circulation
  k : ℕ
  lay : Stage1Layout
  pCostSign : ℕ
  pCostLens : ℕ
  capLimbs : List (List ℕ)
  s : NarrowCostState I.compress
  flowLimbs : Fin I.m → List ℕ
  oldResFwd : Fin I.m → List ℕ
  oldLens : List ℕ

def stage1RoundResCapsCallSpec (w : ℕ) : Spec S1RoundResCapsArg where
  pre := fun g args =>
    let K_cap := bitScalingPhases g.I / g.k + 2
    let C := g.I.compress
    ⌜args = [g.lay.pCtx] ∧
      1 ≤ g.k ∧ 2 * g.k ≤ w ∧ K_cap < 2 ^ w ∧
      g.oldLens.length = 2 * g.I.m ∧
      g.lay.pCapBuf + g.I.m * K_cap < 2 ^ w ∧
      g.lay.pFlow + g.I.m * K_cap < 2 ^ w ∧
      g.lay.pResFwdBuf + g.I.m * K_cap < 2 ^ w ∧
      (∀ e : Fin g.I.m, Limbs g.k (padLimbs K_cap (g.capLimbs.getD e.val [])) ∧
        (padLimbs K_cap (g.capLimbs.getD e.val [])).length = K_cap ∧
        Nat.ofDigits (2 ^ g.k) (padLimbs K_cap (g.capLimbs.getD e.val [])) = C.capacity e) ∧
      (∀ e : Fin g.I.m, Limbs g.k (g.flowLimbs e) ∧ (g.flowLimbs e).length = K_cap ∧
        Nat.ofDigits (2 ^ g.k) (g.flowLimbs e) = (g.s.flow e).toNat ∧
        (g.s.flow e).toNat ≤ C.capacity e) ∧
      (∀ e : Fin g.I.m, (g.oldResFwd e).length = K_cap)⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pCapBuf + e * K_cap)
      (padLimbs K_cap (g.capLimbs.getD e []))) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
      (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap)
      (if h : e < g.I.m then g.oldResFwd ⟨e, h⟩ else [])) *
    Assn.list g.lay.pResCapLens g.oldLens
  post := fun g args v =>
    let K_cap := bitScalingPhases g.I / g.k + 2
    let C := g.I.compress
    let resFwd : Fin g.I.m → List ℕ := fun e =>
      subLimbs g.k (padLimbs K_cap (g.capLimbs.getD e.val [])) (g.flowLimbs e)
    let fwdLens := List.ofFn fun e : Fin g.I.m => canonLen (resFwd e)
    let revLens := List.ofFn fun e : Fin g.I.m => canonLen (g.flowLimbs e)
    ⌜args = [g.lay.pCtx] ∧ v = 0 ∧
      (∀ e : Fin g.I.m, Limbs g.k (resFwd e) ∧ (resFwd e).length = K_cap ∧
        Nat.ofDigits (2 ^ g.k) (resFwd e) = C.capacity e - (g.s.flow e).toNat)⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pCapBuf + e * K_cap)
      (padLimbs K_cap (g.capLimbs.getD e []))) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
      (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap)
      (if h : e < g.I.m then resFwd ⟨e, h⟩ else [])) *
    Assn.list g.lay.pResCapLens (fwdLens ++ revLens)

private def s1ResCapBody (g : S1RoundResCapsArg) : Assn :=
  let K_cap := bitScalingPhases g.I / g.k + 2
  (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pCapBuf + e * K_cap)
    (padLimbs K_cap (g.capLimbs.getD e []))) *
  (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
    (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
  (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap)
    (if h : e < g.I.m then g.oldResFwd ⟨e, h⟩ else [])) *
  Assn.list g.lay.pResCapLens g.oldLens

private theorem s1ResCapBody_eq (g : S1RoundResCapsArg) :
    let K_cap := bitScalingPhases g.I / g.k + 2
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pCapBuf + e * K_cap)
      (padLimbs K_cap (g.capLimbs.getD e []))) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
      (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap)
      (if h : e < g.I.m then g.oldResFwd ⟨e, h⟩ else [])) *
    Assn.list g.lay.pResCapLens g.oldLens = s1ResCapBody g := rfl

theorem stage1RoundResCapsCall_meets {w : ℕ} {p : Program} {f resCapsIdx : ℕ}
    (hp : p.procs[f]? = some (stage1RoundResCapsCall resCapsIdx))
    (hrc : Meets w p resCapsIdx ((stage1ResCapsSpec w).withCost fun g _ =>
      (320 * g.K_cap + 230) * g.m + 40)) :
    Meets w p f ((stage1RoundResCapsCallSpec w).withCost fun g _ =>
      (320 * (bitScalingPhases g.I / g.k + 2) + 230) * g.I.m + 120) := by
  sep_enter g with hk h2k hKlt hol hcf hff hrf hcapS hflS holdR
  set K_cap := bitScalingPhases g.I / g.k + 2
  have hcap_prod :
      (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pCapBuf + e * K_cap)
        (padLimbs K_cap (g.capLimbs.getD e []))) =
      ∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pCapBuf + e * K_cap)
        (if h : e < g.I.m then padLimbs K_cap (g.capLimbs.getD e []) else []) :=
    Finset.prod_congr rfl fun e he => by simp [Finset.mem_range.mp he]
  sep_apply s1ResCapBody_eq g
  sep_apply s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens
  iterate 7 sep_step
  subst m k Kcap pCapBuf pFlow pResFwdBuf pResIn
  sep_step
  subst pResCapLens
  sep_apply (s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens).symm
  sep_apply (s1ResCapBody_eq g).symm
  sep_apply hcap_prod
  sep_step from ⟨g.I.m, g.k, K_cap, g.I.compress.capacity,
    fun e => padLimbs K_cap (g.capLimbs.getD e.val []),
    fun e => (g.s.flow e).toNat, g.flowLimbs, g.oldResFwd, g.oldLens⟩
  sep_apply hcap_prod.symm
  sep_run

/-! ### 3. `stage1RoundBitScaleCall` -/

/-- Load `pResIn` from `pCtx`, set `pResOut := pResIn + 9`, and invoke Stage 2 `bitScale`. -/
wram_def stage1RoundBitScaleCall (bitScaleIdx : ℕ) (pCtx, curH) {
  pResIn := mem[pCtx + 23]
  pResOut := pResIn + 9
  h1 := bitScaleIdx(pResIn, pResOut, curH)
  return h1
}

structure S1RoundBitScaleArg where
  I : Circulation
  k : ℕ
  lay : Stage1Layout
  pCostSign : ℕ
  pCostLens : ℕ
  s : NarrowCostState I.compress
  flowLimbs : Fin I.m → List ℕ
  resFwd : Fin I.m → List ℕ
  resOutOld : List ℕ

def stage1RoundBitScaleCallSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec S1RoundBitScaleArg where
  pre := fun g args => ⨆ curH : ℕ,
    let C := g.I.compress
    let J := narrowRoundInstance C g.s
    let K_cap := bitScalingPhases g.I / g.k + 2
    let tList := List.ofFn fun e : Fin g.I.m => (C.tail e).val
    let hList := List.ofFn fun e : Fin g.I.m => (C.head e).val
    let fwdPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pResFwdBuf + e.val * K_cap
    let revPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pFlow + e.val * K_cap
    let fwdLens := List.ofFn fun e : Fin g.I.m => canonLen (g.resFwd e)
    let revLens := List.ofFn fun e : Fin g.I.m => canonLen (g.flowLimbs e)
    ⌜args = [g.lay.pCtx, curH] ∧ g.lay.pResOut = g.lay.pResIn + 9 ∧
      g.lay.pResIn + 13 < 2 ^ w ∧
      g.resOutOld.length = 4 ∧
      (∀ e : Fin g.I.m, 0 ≤ g.s.flow e ∧ g.s.flow e ≤ (C.capacity e : ℤ)) ∧
      (∀ e : Fin g.I.m, Limbs g.k (g.resFwd e) ∧ (g.resFwd e).length = K_cap ∧
        Nat.ofDigits (2 ^ g.k) (g.resFwd e) = C.capacity e - (g.s.flow e).toNat) ∧
      (∀ e : Fin g.I.m, Limbs g.k (g.flowLimbs e) ∧ (g.flowLimbs e).length = K_cap ∧
        Nat.ofDigits (2 ^ g.k) (g.flowLimbs e) = (g.s.flow e).toNat) ∧
      K_cap * g.k < 2 ^ w ∧
      1 ≤ g.k ∧ 2 * g.k ≤ w ∧ g.k + Nat.log 2 (2 * g.k) + 2 ≤ w ∧
      2 * g.I.m + 1 < 2 ^ g.k ∧ 10 * g.I.m + 9 < 2 ^ w ∧ C.n + 1 < 2 ^ w ∧
      J.CostsBounded ((4 * g.I.m) ^ 10) ∧ (∀ a, (J.cost a).natAbs < 2 ^ w) ∧
      curH + bitScaleSpace J g.k S < 2 ^ w⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    Assn.list g.lay.pResOut g.resOutOld *
    Assn.list g.lay.pResTail (tList ++ hList) *
    Assn.list g.lay.pResHead (hList ++ tList) *
    Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
      if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
    Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
      (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
    Assn.list g.lay.pResCapPtrs (fwdPtrs ++ revPtrs) *
    Assn.list g.lay.pResCapLens (fwdLens ++ revLens) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap)
      (if h : e < g.I.m then g.resFwd ⟨e, h⟩ else [])) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
      (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
    Assn.free curH (2 ^ w - curH)
  post := fun g args h1 => ⨆ (curH : ℕ) (delta : Fin (g.I.m + g.I.m) → ℤ)
      (deltaLimbs : Fin (g.I.m + g.I.m) → List ℕ),
    let C := g.I.compress
    let J := narrowRoundInstance C g.s
    let T_r := bitScalingPhases J
    let L_r := T_r / g.k + 2
    let pRho := curH
    let pGCap := curH + 2 * g.I.m
    let pDelta := curH + 4 * g.I.m
    let K_cap := bitScalingPhases g.I / g.k + 2
    let tList := List.ofFn fun e : Fin g.I.m => (C.tail e).val
    let hList := List.ofFn fun e : Fin g.I.m => (C.head e).val
    let fwdPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pResFwdBuf + e.val * K_cap
    let revPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pFlow + e.val * K_cap
    let fwdLens := List.ofFn fun e : Fin g.I.m => canonLen (g.resFwd e)
    let revLens := List.ofFn fun e : Fin g.I.m => canonLen (g.flowLimbs e)
    ⌜args = [g.lay.pCtx, curH] ∧ curH ≤ h1 ∧ h1 ≤ curH + bitScaleSpace J g.k S ∧
      J.Optimal (fun a => (delta a : ℝ)) ∧
      (∀ a, 0 ≤ delta a ∧ Limbs g.k (deltaLimbs a) ∧ (deltaLimbs a).length = L_r ∧
        ((Nat.ofDigits (2 ^ g.k) (deltaLimbs a) : ℕ) : ℤ) = delta a) ∧
      (∀ a, (0 < cappedResidual J T_r T_r delta (J.m + 1) a ↔
          0 < (J.residual delta).capacity (Fin.castAdd J.m a)) ∧
        (0 < cappedFlow delta (J.m + 1) a ↔
          0 < (J.residual delta).capacity (Fin.natAdd J.m a)))⌝ *
    s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens *
    Assn.list g.lay.pResOut [pDelta, L_r, pRho, pGCap] *
    Assn.list g.lay.pResTail (tList ++ hList) *
    Assn.list g.lay.pResHead (hList ++ tList) *
    Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
      if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
    Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
      (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
    Assn.list g.lay.pResCapPtrs (fwdPtrs ++ revPtrs) *
    Assn.list g.lay.pResCapLens (fwdLens ++ revLens) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap)
      (if h : e < g.I.m then g.resFwd ⟨e, h⟩ else [])) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
      (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
    Assn.list pRho (List.ofFn fun a => cappedResidual J T_r T_r delta (J.m + 1) a) *
    Assn.list pGCap (List.ofFn fun a => cappedFlow delta (J.m + 1) a) *
    (∏ a ∈ Finset.range (g.I.m + g.I.m), Assn.list (pDelta + a * L_r)
      (if h : a < g.I.m + g.I.m then deltaLimbs ⟨a, h⟩ else [])) *
    Assn.free h1 (2 ^ w - h1)

private def s1BSBody (w : ℕ) (g : S1RoundBitScaleArg) (curH : ℕ) : Assn :=
  let C := g.I.compress
  let K_cap := bitScalingPhases g.I / g.k + 2
  let tList := List.ofFn fun e : Fin g.I.m => (C.tail e).val
  let hList := List.ofFn fun e : Fin g.I.m => (C.head e).val
  let fwdPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pResFwdBuf + e.val * K_cap
  let revPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pFlow + e.val * K_cap
  let fwdLens := List.ofFn fun e : Fin g.I.m => canonLen (g.resFwd e)
  let revLens := List.ofFn fun e : Fin g.I.m => canonLen (g.flowLimbs e)
  Assn.list g.lay.pResOut g.resOutOld *
  Assn.list g.lay.pResTail (tList ++ hList) *
  Assn.list g.lay.pResHead (hList ++ tList) *
  Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
    if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
  Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
    (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
  Assn.list g.lay.pResCapPtrs (fwdPtrs ++ revPtrs) *
  Assn.list g.lay.pResCapLens (fwdLens ++ revLens) *
  (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap)
    (if h : e < g.I.m then g.resFwd ⟨e, h⟩ else [])) *
  (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
    (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
  Assn.free curH (2 ^ w - curH)

private theorem s1BSBody_eq (w : ℕ) (g : S1RoundBitScaleArg) (curH : ℕ) :
    let C := g.I.compress
    let K_cap := bitScalingPhases g.I / g.k + 2
    let tList := List.ofFn fun e : Fin g.I.m => (C.tail e).val
    let hList := List.ofFn fun e : Fin g.I.m => (C.head e).val
    let fwdPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pResFwdBuf + e.val * K_cap
    let revPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pFlow + e.val * K_cap
    let fwdLens := List.ofFn fun e : Fin g.I.m => canonLen (g.resFwd e)
    let revLens := List.ofFn fun e : Fin g.I.m => canonLen (g.flowLimbs e)
    Assn.list g.lay.pResOut g.resOutOld *
    Assn.list g.lay.pResTail (tList ++ hList) *
    Assn.list g.lay.pResHead (hList ++ tList) *
    Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
      if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
    Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
      (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
    Assn.list g.lay.pResCapPtrs (fwdPtrs ++ revPtrs) *
    Assn.list g.lay.pResCapLens (fwdLens ++ revLens) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap)
      (if h : e < g.I.m then g.resFwd ⟨e, h⟩ else [])) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
      (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) *
    Assn.free curH (2 ^ w - curH) = s1BSBody w g curH := rfl

private theorem s1BS_pack_input (g : S1RoundBitScaleArg)
    (hrLen : ∀ e, (g.resFwd e).length = bitScalingPhases g.I / g.k + 2)
    (hfLen : ∀ e, (g.flowLimbs e).length = bitScalingPhases g.I / g.k + 2) :
    let C := g.I.compress
    let J := narrowRoundInstance C g.s
    let K_cap := bitScalingPhases g.I / g.k + 2
    let tList := List.ofFn fun e : Fin g.I.m => (C.tail e).val
    let hList := List.ofFn fun e : Fin g.I.m => (C.head e).val
    let fwdPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pResFwdBuf + e.val * K_cap
    let revPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pFlow + e.val * K_cap
    let fwdLens := List.ofFn fun e : Fin g.I.m => canonLen (g.resFwd e)
    let revLens := List.ofFn fun e : Fin g.I.m => canonLen (g.flowLimbs e)
    Assn.list g.lay.pResIn
      [C.n, 2 * g.I.m, g.k, g.lay.pResTail, g.lay.pResHead, g.lay.pResCSign, g.lay.pResCMag,
       g.lay.pResCapPtrs, g.lay.pResCapLens] *
    Assn.list g.lay.pResTail (tList ++ hList) *
    Assn.list g.lay.pResHead (hList ++ tList) *
    Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
      if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
    Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
      (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
    Assn.list g.lay.pResCapPtrs (fwdPtrs ++ revPtrs) *
    Assn.list g.lay.pResCapLens (fwdLens ++ revLens) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap)
      (if h : e < g.I.m then g.resFwd ⟨e, h⟩ else [])) *
    (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap)
      (if h : e < g.I.m then g.flowLimbs ⟨e, h⟩ else [])) =
    bitScaleInput J g.k (fwdPtrs ++ revPtrs) (resCapCanonLimbs g.resFwd g.flowLimbs)
      g.lay.pResIn g.lay.pResTail g.lay.pResHead g.lay.pResCSign g.lay.pResCMag
      g.lay.pResCapPtrs g.lay.pResCapLens *
    (∏ e ∈ Finset.range g.I.m,
      Assn.list (g.lay.pResFwdBuf + e * K_cap + (if h : e < g.I.m then canonLen (g.resFwd ⟨e, h⟩) else 0))
        (List.replicate (K_cap - if h : e < g.I.m then canonLen (g.resFwd ⟨e, h⟩) else 0) 0)) *
    (∏ e ∈ Finset.range g.I.m,
      Assn.list (g.lay.pFlow + e * K_cap + (if h : e < g.I.m then canonLen (g.flowLimbs ⟨e, h⟩) else 0))
        (List.replicate (K_cap - if h : e < g.I.m then canonLen (g.flowLimbs ⟨e, h⟩) else 0) 0)) := by
  intro C J K_cap tList hList fwdPtrs revPtrs fwdLens revLens
  have hsp := stage1ResCaps_split_for_bitScale (pResFwdBuf := g.lay.pResFwdBuf)
    (pFlow := g.lay.pFlow) g.resFwd g.flowLimbs hrLen hfLen
  have hlen : (resCapCanonLimbs g.resFwd g.flowLimbs).map List.length = fwdLens ++ revLens :=
    resCapCanonLimbs_map_length g.resFwd g.flowLimbs K_cap hrLen hfLen
  have ht := narrowRound_tail_list C g.s
  have hh := narrowRound_head_list C g.s
  have hm2 : J.m = 2 * g.I.m := by change g.I.m + g.I.m = 2 * g.I.m; omega
  have hbs_eq :
      bitScaleInput J g.k (fwdPtrs ++ revPtrs) (resCapCanonLimbs g.resFwd g.flowLimbs)
        g.lay.pResIn g.lay.pResTail g.lay.pResHead g.lay.pResCSign g.lay.pResCMag
        g.lay.pResCapPtrs g.lay.pResCapLens =
      Assn.list g.lay.pResIn
        [C.n, 2 * g.I.m, g.k, g.lay.pResTail, g.lay.pResHead, g.lay.pResCSign, g.lay.pResCMag,
         g.lay.pResCapPtrs, g.lay.pResCapLens] *
      Assn.list g.lay.pResTail (tList ++ hList) *
      Assn.list g.lay.pResHead (hList ++ tList) *
      Assn.list g.lay.pResCSign (List.ofFn fun a : Fin (C.m + C.m) =>
        if narrowRoundedCosts C g.s.frozen g.s.halfCost a < 0 then 1 else 0) *
      Assn.list g.lay.pResCMag (List.ofFn fun a : Fin (C.m + C.m) =>
        (narrowRoundedCosts C g.s.frozen g.s.halfCost a).natAbs) *
      Assn.list g.lay.pResCapPtrs (fwdPtrs ++ revPtrs) *
      Assn.list g.lay.pResCapLens (fwdLens ++ revLens) *
      (∏ a ∈ Finset.range (2 * g.I.m),
        Assn.list ((fwdPtrs ++ revPtrs).getD a 0) ((resCapCanonLimbs g.resFwd g.flowLimbs).getD a [])) := by
    unfold bitScaleInput
    rw [ht, hh, hlen]
    refine congrArg₂ (· * ·) ?_ (by rw [hm2])
    refine congrArg₂ (· * ·) ?_ rfl
    refine congrArg₂ (· * ·) ?_ rfl
    refine congrArg₂ (· * ·) ?_ rfl
    refine congrArg₂ (· * ·) ?_ rfl
    refine congrArg₂ (· * ·) ?_ rfl
    refine congrArg₂ (· * ·) ?_ rfl
    rw [hm2]
  rw [hbs_eq]
  change _ * (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap) _) *
      (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pFlow + e * K_cap) _) = _
  rw [mul_assoc _ (∏ e ∈ Finset.range g.I.m, Assn.list (g.lay.pResFwdBuf + e * K_cap) _), hsp]
  simp only [mul_assoc]
  rfl

theorem stage1RoundBitScaleCall_meets {w : ℕ} {p : Program} {f bitScaleIdx : ℕ}
    {S : ℕ → ℕ → ℕ} {T_bs : Circulation → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage1RoundBitScaleCall bitScaleIdx))
    (hbs : Meets w p bitScaleIdx ((bitScaleSpec w S).withCost fun d _ => T_bs d.I d.k)) :
    Meets w p f ((stage1RoundBitScaleCallSpec w S).withCost fun g _ =>
      T_bs (narrowRoundInstance g.I.compress g.s) g.k + 40) := by
  sep_enter g with hresOut hresIn13 hout4 hflowFeas hresSpec hflSpec hKk hk h2k hkw h2mk h10m hn1 hJcostB hJcostW hsp
  set C := g.I.compress
  set J := narrowRoundInstance C g.s
  set K_cap := bitScalingPhases g.I / g.k + 2
  set fwdPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pResFwdBuf + e.val * K_cap
  set revPtrs := List.ofFn fun e : Fin g.I.m => g.lay.pFlow + e.val * K_cap
  set canonLimbs := resCapCanonLimbs g.resFwd g.flowLimbs
  have hJm : J.m = 2 * g.I.m := by change g.I.m + g.I.m = 2 * g.I.m; omega
  have hcaps_ok : ∀ a (ha : a < J.m),
      CanonicalLimbs g.k (canonLimbs.getD a []) ∧
      (canonLimbs.getD a []).length * g.k < 2 ^ w ∧
      Nat.ofDigits (2 ^ g.k) (canonLimbs.getD a []) = J.capacity ⟨a, ha⟩ := by
    intro a ha
    by_cases hlt : a < g.I.m
    · have hget : canonLimbs.getD a [] = (g.resFwd ⟨a, hlt⟩).take (canonLen (g.resFwd ⟨a, hlt⟩)) := by
        dsimp only [canonLimbs, resCapCanonLimbs]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega),
          List.getElem_ofFn]
      rw [hget]
      have hlen_le : ((g.resFwd ⟨a, hlt⟩).take (canonLen (g.resFwd ⟨a, hlt⟩))).length ≤ K_cap := by
        rw [List.length_take, (hresSpec ⟨a, hlt⟩).2.1]; exact Nat.min_le_right _ _
      have hfin : (⟨a, ha⟩ : Fin (C.m + C.m)) = Fin.castAdd C.m ⟨a, hlt⟩ := by ext; rfl
      refine ⟨canonicalLimbs_take_canonLen (hresSpec ⟨a, hlt⟩).1,
        lt_of_le_of_lt (Nat.mul_le_mul_right g.k hlen_le) hKk, ?_⟩
      rw [ofDigits_take_canonLen, (hresSpec ⟨a, hlt⟩).2.2]
      change C.capacity ⟨a, hlt⟩ - (g.s.flow ⟨a, hlt⟩).toNat = (C.residual g.s.flow).capacity ⟨a, ha⟩
      rw [hfin]; simp only [Fin.addCases_left]
      have := hflowFeas ⟨a, hlt⟩; omega
    · have hlt2 : a - g.I.m < g.I.m := by omega
      have hget : canonLimbs.getD a [] =
          (g.flowLimbs ⟨a - g.I.m, hlt2⟩).take (canonLen (g.flowLimbs ⟨a - g.I.m, hlt2⟩)) := by
        dsimp only [canonLimbs, resCapCanonLimbs]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp
      rw [hget]
      have hlen_le : ((g.flowLimbs ⟨a - g.I.m, hlt2⟩).take
          (canonLen (g.flowLimbs ⟨a - g.I.m, hlt2⟩))).length ≤ K_cap := by
        rw [List.length_take, (hflSpec ⟨a - g.I.m, hlt2⟩).2.1]; exact Nat.min_le_right _ _
      have hfin : (⟨a, ha⟩ : Fin (C.m + C.m)) = Fin.natAdd C.m ⟨a - g.I.m, hlt2⟩ := by
        ext; change a = g.I.m + (a - g.I.m); omega
      refine ⟨canonicalLimbs_take_canonLen (hflSpec ⟨a - g.I.m, hlt2⟩).1,
        lt_of_le_of_lt (Nat.mul_le_mul_right g.k hlen_le) hKk, ?_⟩
      rw [ofDigits_take_canonLen, (hflSpec ⟨a - g.I.m, hlt2⟩).2.2]
      change (g.s.flow ⟨a - g.I.m, hlt2⟩).toNat = (C.residual g.s.flow).capacity ⟨a, ha⟩
      rw [hfin]; simp only [Fin.addCases_right]
  have hcb_J : J.CostsBounded ((2 * J.m) ^ 10) := by
    intro a; rw [hJm, show 2 * (2 * g.I.m) = 4 * g.I.m by omega]; exact hJcostB a
  sep_apply s1BSBody_eq w g curH
  sep_apply s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens
  sep_step
  subst pResIn
  sep_step
  subst pResOut
  dsimp only [List.getElem_cons_succ, List.getElem_cons_zero]
  rw [← hresOut]
  sep_apply (s1CtxHdr_split g.I g.k g.lay g.pCostSign g.pCostLens).symm
  sep_apply (s1BSBody_eq w g curH).symm
  unfold s1CtxHdr
  sep_apply s1BS_pack_input g (fun e => (hresSpec e).2.1) (fun e => (hflSpec e).2.1)
  sep_step from (⟨J, g.k, fwdPtrs ++ revPtrs, canonLimbs,
    ⟨g.lay.pResTail, g.lay.pResHead, g.lay.pResCSign, g.lay.pResCMag, g.lay.pResCapPtrs, g.lay.pResCapLens⟩,
    g.resOutOld⟩ : BitScaleData)
  sep_apply (s1BS_pack_input g (fun e => (hresSpec e).2.1) (fun e => (hflSpec e).2.1)).symm
  have hctx_fold :
      Assn.list g.lay.pCtx (stage1CtxWords g.I g.k g.lay g.pCostSign g.pCostLens) *
      Assn.list g.lay.pResIn
        [C.n, 2 * g.I.m, g.k, g.lay.pResTail, g.lay.pResHead, g.lay.pResCSign, g.lay.pResCMag,
         g.lay.pResCapPtrs, g.lay.pResCapLens] =
      s1CtxHdr g.I g.k g.lay g.pCostSign g.pCostLens := rfl
  sep_apply hctx_fold
  have h2m_eq : curH + 2 * J.m = curH + 4 * g.I.m := by rw [hJm]; omega
  have hm_eq : curH + J.m = curH + 2 * g.I.m := by rw [hJm]
  rw [h2m_eq, hm_eq]
  sep_run
  · simp [fwdPtrs, revPtrs, hJm]; omega
  · simp [canonLimbs, resCapCanonLimbs, hJm]; omega

end MinCostFlow.NarrowProg.Stage1
