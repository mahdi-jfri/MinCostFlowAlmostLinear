module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import WordRAM.Std.Array
public import WordRAM.Std.Bits
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1StartHelpers
public import MinCostFlow.NarrowProg.Stage1Layout
public import MinCostFlow.NarrowProg.Stage1StartHdr
public import MinCostFlow.NarrowProg.Stage1StartInit
public import MinCostFlow.NarrowProg.TopBitLength
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Top-level Stage 1 startup (`stage1Start`) and module

Composes `stage1StartHdr`, `stage1InitHalfCosts`, `stage1InitResEndpoints`,
`stage1InitCapTables`, and `stage1InitAdjCosts` into `stage1Start`, establishing
`stage1Start_meets`, `stage1Start_meetsO`, and the polymorphic `stage1StartMod`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow
  MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate

private theorem free_merge_left {a b c d s : ℕ} (h1 : a + b = c) (h2 : b + d = s) :
    Assn.free a b * Assn.free c d = Assn.free a s := by
  subst h1; subst h2; exact (Assn.free_add' a b d).symm

private def s1ResEpZero (lay : Stage1Layout) (m : ℕ) : Assn :=
  Assn.list lay.pResTail (List.replicate m 0) *
  Assn.list (lay.pResTail + m) (List.replicate m 0) *
  Assn.list lay.pResHead (List.replicate m 0) *
  Assn.list (lay.pResHead + m) (List.replicate m 0)

private def s1CapTabZero (lay : Stage1Layout) (m K_cap : ℕ) : Assn :=
  Assn.list lay.pResCapPtrs (List.replicate m 0) *
  Assn.list (lay.pResCapPtrs + m) (List.replicate m 0) *
  (∏ j ∈ Finset.range m, Assn.list (lay.pCapBuf + j * K_cap) (List.replicate K_cap 0))

private def s1RestZero (lay : Stage1Layout) (m K_cap : ℕ) : Assn :=
  Assn.list lay.pFrozen (List.replicate m 0) *
  Assn.list lay.pResCSign (List.replicate (2 * m) 0) *
  Assn.list lay.pResCMag (List.replicate (2 * m) 0) *
  Assn.list lay.pResCapLens (List.replicate (2 * m) 0) *
  (∏ j ∈ Finset.range m, Assn.list (lay.pFlow + j * K_cap) (List.replicate K_cap 0)) *
  (∏ j ∈ Finset.range m, Assn.list (lay.pResFwdBuf + j * K_cap) (List.replicate K_cap 0)) *
  Assn.list lay.pTmp1 (List.replicate K_cap 0) *
  Assn.list lay.pTmp2 (List.replicate K_cap 0)

private lemma perm19 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 : Assn} :
    a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 =
      a3 * a4 * (a5 * a6 * a7 * a8) * (a11 * a12 * a14) * a1 *
      (a2 * a9 * a10 * a13 * a15 * a16 * a17 * a18) * a19 := by
  simp only [mul_left_comm, mul_comm]

private lemma perm10 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Assn} :
    a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 =
      a1 * a7 * (a2 * a3) * (a4 * a5 * a6) * (a8 * a9 * a10) := by
  simp only [mul_left_comm, mul_comm]

private lemma perm20 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 : Assn} :
    a1 * a2 * a3 * (a8 * a9) * (a4 * a5 * a10 * a11) * (a14 * a16) *
      (a7 * a12 * a13 * a15 * a17 * a18 * a19 * a20) * a6 * a21 =
    a1 * a2 * a3 * a4 * a5 * a6 * a21 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 *
      a16 * a17 * a18 * a19 * a20 := by
  simp only [mul_left_comm, mul_comm]

private theorem stage1StartInit_free_split {w h n m K_cap : ℕ}
    (hfit : h + 37 + n + 18 * m + 3 * m * K_cap + 2 * K_cap ≤ 2 ^ w) :
    let lay := mkStage1Layout h n m K_cap
    let hMid := h + 37 + n + 2 * m
    let hAfter := h + 37 + n + 18 * m + 3 * m * K_cap + 2 * K_cap
    Assn.free hMid (2 ^ w - hMid) =
      Assn.list lay.pHSign (List.replicate m 0) *
      Assn.list lay.pHMag (List.replicate m 0) *
      s1ResEpZero lay m * s1CapTabZero lay m K_cap *
      Assn.list lay.pAdjCostPtrs (List.replicate m 0) *
      s1RestZero lay m K_cap *
      Assn.free hAfter (2 ^ w - hAfter) := by
  dsimp only [s1ResEpZero, s1CapTabZero, s1RestZero, mkStage1Layout]
  rw [← free_mul_eq_prod, ← free_mul_eq_prod, ← free_mul_eq_prod]
  have hf_eq : ∀ a r : ℕ, Assn.list a (List.replicate r 0) = Assn.free a r := fun _ _ => rfl
  simp only [hf_eq]
  have hflat :
      Assn.free (h + 37 + n + 2 * m) m * Assn.free (h + 37 + n + 3 * m) m *
      Assn.free (h + 37 + n + 4 * m) m * Assn.free (h + 37 + n + 5 * m) m *
      Assn.free (h + 37 + n + 6 * m) m * Assn.free (h + 37 + n + 6 * m + m) m *
      Assn.free (h + 37 + n + 8 * m) m * Assn.free (h + 37 + n + 8 * m + m) m *
      Assn.free (h + 37 + n + 10 * m) (2 * m) * Assn.free (h + 37 + n + 12 * m) (2 * m) *
      Assn.free (h + 37 + n + 14 * m) m * Assn.free (h + 37 + n + 14 * m + m) m *
      Assn.free (h + 37 + n + 16 * m) (2 * m) * Assn.free (h + 37 + n + 18 * m) (m * K_cap) *
      Assn.free (h + 37 + n + 18 * m + m * K_cap) (m * K_cap) *
      Assn.free (h + 37 + n + 18 * m + 2 * m * K_cap) (m * K_cap) *
      Assn.free (h + 37 + n + 18 * m + 3 * m * K_cap) K_cap *
      Assn.free (h + 37 + n + 18 * m + 3 * m * K_cap + K_cap) K_cap *
      Assn.free (h + 37 + n + 18 * m + 3 * m * K_cap + 2 * K_cap)
        (2 ^ w - (h + 37 + n + 18 * m + 3 * m * K_cap + 2 * K_cap)) =
      Assn.free (h + 37 + n + 2 * m) (2 ^ w - (h + 37 + n + 2 * m)) := by
    rw [free_merge_left (s := 2 * m) (by omega) (by omega),
      free_merge_left (s := 3 * m) (by omega) (by omega),
      free_merge_left (s := 4 * m) (by omega) (by omega),
      free_merge_left (s := 5 * m) (by omega) (by omega),
      free_merge_left (s := 6 * m) (by omega) (by omega),
      free_merge_left (s := 7 * m) (by omega) (by omega),
      free_merge_left (s := 8 * m) (by omega) (by omega),
      free_merge_left (s := 10 * m) (by omega) (by omega),
      free_merge_left (s := 12 * m) (by omega) (by omega),
      free_merge_left (s := 13 * m) (by omega) (by omega),
      free_merge_left (s := 14 * m) (by omega) (by omega),
      free_merge_left (s := 16 * m) (by omega) (by omega),
      free_merge_left (s := 16 * m + m * K_cap) (by ring) (by ring),
      free_merge_left (s := 16 * m + 2 * m * K_cap) (by ring) (by ring),
      free_merge_left (s := 16 * m + 3 * m * K_cap) (by ring) (by ring),
      free_merge_left (s := 16 * m + 3 * m * K_cap + K_cap) (by ring) (by ring),
      free_merge_left (s := 16 * m + 3 * m * K_cap + 2 * K_cap) (by ring) (by ring)]
    exact free_merge_left (s := 2 ^ w - (h + 37 + n + 2 * m)) (by ring) (by omega)
  rw [← hflat]; exact perm19

/-- Full Stage 1 startup procedure. -/
wram_def stage1Start (hdrIdx halfIdx resEpIdx capTabIdx adjIdx : ℕ) (pIn, h) {
  hAfter := hdrIdx(pIn, h)
  r := halfIdx(pIn, h)
  r := resEpIdx(h)
  r := capTabIdx(pIn, h)
  curH := adjIdx(pIn, h, hAfter)
  return curH
}

/-- Specification of `stage1Start`: for `0 < I.m`, initializes the Stage 1 working state at
round `0` (`narrowCostInitial I.compress`, zero flows), preserving `stage1Input` and advancing
the heap pointer by at most `stage1StartSpace I k`. -/
def stage1StartSpec (w : ℕ) :
    Spec (Circulation × ℕ × List ℕ × List (List ℕ) × List ℕ × List (List ℕ)) where
  pre := fun (I, k, capPtrs, capLimbs, costPtrs, costLimbs) args =>
    ⨆ (pIn : ℕ) (h : ℕ) (pTail : ℕ) (pHead : ℕ) (pCapPtrs : ℕ) (pCapLens : ℕ)
      (pCostSign : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ),
      ⌜args = [pIn, h] ∧ 0 < I.m ∧
        capPtrs.length = I.m ∧ capLimbs.length = I.m ∧
        costPtrs.length = I.m ∧ costLimbs.length = I.m ∧
        (∀ j (hj : j < I.m), CanonicalLimbs k (capLimbs.getD j []) ∧
          (capLimbs.getD j []).length * k < 2 ^ w ∧
          Nat.ofDigits (2 ^ k) (capLimbs.getD j []) = I.capacity ⟨j, hj⟩) ∧
        (∀ j (hj : j < I.m), CanonicalLimbs k (costLimbs.getD j []) ∧
          (costLimbs.getD j []).length * k < 2 ^ w ∧
          Nat.ofDigits (2 ^ k) (costLimbs.getD j []) = (I.cost ⟨j, hj⟩).natAbs) ∧
        1 ≤ k ∧ 2 * k ≤ w ∧ 2 * I.m + 1 < 2 ^ k ∧
        6 * I.m + 4 < 2 ^ w ∧ I.n + 1 < 2 ^ w ∧
        (6 * I.m + 21) * upperClip I.m < 2 ^ w ∧
        narrowCostRounds I.compress < 2 ^ w ∧
        h + stage1StartSpace I k < 2 ^ w⌝ *
      stage1Input I k capPtrs capLimbs costPtrs costLimbs
        pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens *
      Assn.free h (2 ^ w - h)
  post := fun (I, k, capPtrs, capLimbs, costPtrs, costLimbs) args h' =>
    ⨆ (pIn : ℕ) (h : ℕ) (pTail : ℕ) (pHead : ℕ) (pCapPtrs : ℕ) (pCapLens : ℕ)
      (pCostSign : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ)
      (adjPtrs : List ℕ) (adjLimbs : List (List ℕ)),
      let K_cap := bitScalingPhases I / k + 2
      let lay := mkStage1Layout h I.n I.m K_cap
      ⌜args = [pIn, h] ∧ h ≤ h' ∧ h' ≤ h + stage1StartSpace I k ∧
        adjPtrs.length = I.m ∧ adjLimbs.length = I.m ∧
        (∀ j (hj : j < I.m), Limbs k (adjLimbs.getD j []) ∧
          (adjLimbs.getD j []).length = (costLimbs.getD j []).length ∧
          Nat.ofDigits (2 ^ k) (adjLimbs.getD j []) =
            if I.cost ⟨j, hj⟩ < 0 then (I.cost ⟨j, hj⟩).natAbs - 1 else (I.cost ⟨j, hj⟩).natAbs)⌝ *
      stage1Input I k capPtrs capLimbs costPtrs costLimbs
        pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens *
      Assn.list (h + 37) (List.ofFn I.endpointLabels.table) *
      stage1WorkingAssn I k lay pCostSign pCostLens capLimbs costLimbs adjPtrs adjLimbs
        (narrowCostInitial I.compress) (fun _ => List.replicate K_cap 0)
        (List.replicate (2 * I.m) 0) (List.replicate (2 * I.m) 0)
        (List.replicate (2 * I.m) 0) (List.replicate 4 0)
        (fun _ => List.replicate K_cap 0) (List.replicate K_cap 0) (List.replicate K_cap 0) *
      Assn.free h' (2 ^ w - h')

/-- Explicit cost of `stage1Start`: linear in `m * (K_cap + L_limbs + 1) + T_U + L`. -/
def stage1StartCost (I : Circulation) (k : ℕ) : ℕ :=
  let K_cap := bitScalingPhases I / k + 2
  let L_limbs := costScaleBits I / k + 2
  stage1StartHdrCost I + (40 * I.m + 80) + (75 * I.m + 140) +
    (120 * I.m + 17 * I.m * K_cap + 160) + (100 * I.m + 55 * I.m * L_limbs + 80) + 60

private def s1InEp (I : Circulation) (a2 a3 : ℕ) : Assn :=
  Assn.list a2 (List.ofFn fun e : Fin I.m => (I.tail e).val) *
  Assn.list a3 (List.ofFn fun e : Fin I.m => (I.head e).val)

private def s1InCap (I : Circulation) (capPtrs : List ℕ) (capLimbs : List (List ℕ)) (a4 a5 : ℕ) : Assn :=
  Assn.list a4 capPtrs * Assn.list a5 (capLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j []))

private def s1InCost (I : Circulation) (costPtrs : List ℕ) (costLimbs : List (List ℕ)) (a7 a8 : ℕ) : Assn :=
  Assn.list a7 costPtrs * Assn.list a8 (costLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j []))

private def s1HalfDone (I : Circulation) (lay : Stage1Layout) : Assn :=
  Assn.list lay.pHSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
  Assn.list lay.pHMag (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0)

private def s1ResEpDone (I : Circulation) (lay : Stage1Layout) : Assn :=
  Assn.list lay.pCompTail (List.ofFn fun e : Fin I.m => (I.compress.tail e).val) *
  Assn.list lay.pCompHead (List.ofFn fun e : Fin I.m => (I.compress.head e).val) *
  Assn.list lay.pResTail
    ((List.ofFn fun e : Fin I.m => (I.compress.tail e).val) ++
     (List.ofFn fun e : Fin I.m => (I.compress.head e).val)) *
  Assn.list lay.pResHead
    ((List.ofFn fun e : Fin I.m => (I.compress.head e).val) ++
     (List.ofFn fun e : Fin I.m => (I.compress.tail e).val))

private def s1CapTabDone (I : Circulation) (k : ℕ) (lay : Stage1Layout) (capLimbs : List (List ℕ)) : Assn :=
  let K_cap := bitScalingPhases I / k + 2
  Assn.list lay.pResCapPtrs
    ((List.ofFn fun e : Fin I.m => lay.pResFwdBuf + e.val * K_cap) ++
     (List.ofFn fun e : Fin I.m => lay.pFlow + e.val * K_cap)) *
  (∏ j ∈ Finset.range I.m, Assn.list (lay.pCapBuf + j * K_cap) (padLimbs K_cap (capLimbs.getD j [])))

private theorem s1In_split (I : Circulation) (k : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ)) (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (a1 a2 a3 a4 a5 a6 a7 a8 : ℕ) :
    stage1Input I k capPtrs capLimbs costPtrs costLimbs a1 a2 a3 a4 a5 a6 a7 a8 =
      Assn.list a1 [I.n, I.m, k, a2, a3, a4, a5, a6, a7, a8] *
      Assn.list a6 (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
      s1InEp I a2 a3 * s1InCap I capPtrs capLimbs a4 a5 * s1InCost I costPtrs costLimbs a7 a8 := by
  unfold stage1Input s1InEp s1InCap s1InCost; exact perm10

private theorem s1CapsHdr_fold (I : Circulation) (k : ℕ) (lay : Stage1Layout) (ptrs : Stage1HdrPtrs) :
    Assn.list ptrs.pIn [I.n, I.m, k, ptrs.pTail, ptrs.pHead, ptrs.pCapPtrs, ptrs.pCapLens,
      ptrs.pCostSign, ptrs.pCostPtrs, ptrs.pCostLens] *
    Assn.list lay.pCtx (stage1CtxWords I k lay ptrs.pCostSign ptrs.pCostLens) *
    Assn.list lay.pResIn
      [I.compress.n, 2 * I.m, k, lay.pResTail, lay.pResHead, lay.pResCSign, lay.pResCMag,
       lay.pResCapPtrs, lay.pResCapLens] = s1CapsHdr I k lay ptrs := rfl

private theorem s1ResEpZero_eq (lay : Stage1Layout) (m : ℕ) :
    s1ResEpZero lay m =
      Assn.list lay.pResTail (List.replicate m 0) * Assn.list (lay.pResTail + m) (List.replicate m 0) *
      Assn.list lay.pResHead (List.replicate m 0) * Assn.list (lay.pResHead + m) (List.replicate m 0) := rfl

private theorem s1CapTabZero_eq (lay : Stage1Layout) (m K_cap : ℕ) :
    s1CapTabZero lay m K_cap =
      Assn.list lay.pResCapPtrs (List.replicate m 0) *
      Assn.list (lay.pResCapPtrs + m) (List.replicate m 0) *
      (∏ j ∈ Finset.range m, Assn.list (lay.pCapBuf + j * K_cap) (List.replicate K_cap 0)) := rfl

private theorem s1InCap_eq (I : Circulation) (capPtrs : List ℕ) (capLimbs : List (List ℕ)) (a4 a5 : ℕ) :
    s1InCap I capPtrs capLimbs a4 a5 =
      Assn.list a4 capPtrs * Assn.list a5 (capLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) := rfl

private theorem s1InCost_eq (I : Circulation) (costPtrs : List ℕ) (costLimbs : List (List ℕ)) (a7 a8 : ℕ) :
    s1InCost I costPtrs costLimbs a7 a8 =
      Assn.list a7 costPtrs * Assn.list a8 (costLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])) := rfl

private theorem s1HalfDone_eq (I : Circulation) (lay : Stage1Layout) :
    Assn.list lay.pHSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
    Assn.list lay.pHMag (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) =
    s1HalfDone I lay := rfl

private theorem s1ResEpDone_eq (I : Circulation) (lay : Stage1Layout) :
    Assn.list lay.pCompTail (List.ofFn fun e : Fin I.m => (I.compress.tail e).val) *
    Assn.list lay.pCompHead (List.ofFn fun e : Fin I.m => (I.compress.head e).val) *
    Assn.list lay.pResTail
      ((List.ofFn fun e : Fin I.m => (I.compress.tail e).val) ++
       (List.ofFn fun e : Fin I.m => (I.compress.head e).val)) *
    Assn.list lay.pResHead
      ((List.ofFn fun e : Fin I.m => (I.compress.head e).val) ++
       (List.ofFn fun e : Fin I.m => (I.compress.tail e).val)) =
    s1ResEpDone I lay := rfl

private theorem s1CapTabDone_eq (I : Circulation) (k : ℕ) (lay : Stage1Layout) (capLimbs : List (List ℕ)) :
    let K_cap := bitScalingPhases I / k + 2
    Assn.list lay.pResCapPtrs
      ((List.ofFn fun e : Fin I.m => lay.pResFwdBuf + e.val * K_cap) ++
       (List.ofFn fun e : Fin I.m => lay.pFlow + e.val * K_cap)) *
    (∏ j ∈ Finset.range I.m, Assn.list (lay.pCapBuf + j * K_cap) (padLimbs K_cap (capLimbs.getD j []))) =
    s1CapTabDone I k lay capLimbs := rfl

private theorem stage1Start_fold_work (I : Circulation) (k : ℕ) (lay : Stage1Layout)
    (a6 a8 : ℕ) (capLimbs costLimbs : List (List ℕ)) (adjPtrs : List ℕ) (adjLimbs : List (List ℕ))
    (hcol : costLimbs.length = I.m) (hadjP : adjPtrs.length = I.m) (hadjL : adjLimbs.length = I.m) :
    let K_cap := bitScalingPhases I / k + 2
    Assn.list lay.pCtx (stage1CtxWords I k lay a6 a8) *
    Assn.list lay.pResIn
      [I.compress.n, 2 * I.m, k, lay.pResTail, lay.pResHead, lay.pResCSign, lay.pResCMag,
       lay.pResCapPtrs, lay.pResCapLens] *
    Assn.list lay.pResOut (List.replicate 4 0) *
    s1HalfDone I lay * s1ResEpDone I lay * s1CapTabDone I k lay capLimbs *
    s1RestZero lay I.m K_cap *
    Assn.list lay.pAdjCostPtrs adjPtrs *
    (∏ j ∈ Finset.range I.m, Assn.list (adjPtrs.getD j 0) (adjLimbs.getD j [])) =
    stage1WorkingAssn I k lay a6 a8 capLimbs costLimbs adjPtrs adjLimbs
      (narrowCostInitial I.compress) (fun _ => List.replicate K_cap 0)
      (List.replicate (2 * I.m) 0) (List.replicate (2 * I.m) 0)
      (List.replicate (2 * I.m) 0) (List.replicate 4 0)
      (fun _ => List.replicate K_cap 0) (List.replicate K_cap 0) (List.replicate K_cap 0) := by
  intro K_cap
  have hinit_frozen : (List.ofFn fun e : Fin I.m => freezeCode ((narrowCostInitial I.compress).frozen e)) =
      List.replicate I.m 0 := by
    refine List.ext_getElem (by simp) fun i hi1 hi2 => by simp [narrowCostInitial, freezeCode]
  have hinit_hsign : (List.ofFn fun e : Fin I.m => if (narrowCostInitial I.compress).halfCost e < 0 then 1 else 0) =
      List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0 := by
    refine List.ext_getElem (by simp) fun i hi1 hi2 => by
      simp only [List.getElem_ofFn, narrowCostInitial, Circulation.compress]; split_ifs <;> omega
  have hinit_hmag : (List.ofFn fun e : Fin I.m => ((narrowCostInitial I.compress).halfCost e).natAbs) =
      List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0 := by
    refine List.ext_getElem (by simp) fun i hi1 hi2 => by
      simp only [List.getElem_ofFn, narrowCostInitial, Circulation.compress]; split_ifs <;> simp
  have hinit_flow : (∏ j ∈ Finset.range I.m, Assn.list (lay.pFlow + j * K_cap) (List.replicate K_cap 0)) =
      ∏ j ∈ Finset.range I.m, Assn.list (lay.pFlow + j * K_cap)
        (if _ : j < I.m then List.replicate K_cap 0 else []) :=
    Finset.prod_congr rfl fun j hj => by simp [Finset.mem_range.mp hj]
  have hinit_res : (∏ j ∈ Finset.range I.m, Assn.list (lay.pResFwdBuf + j * K_cap) (List.replicate K_cap 0)) =
      ∏ j ∈ Finset.range I.m, Assn.list (lay.pResFwdBuf + j * K_cap)
        (if _ : j < I.m then List.replicate K_cap 0 else []) :=
    Finset.prod_congr rfl fun j hj => by simp [Finset.mem_range.mp hj]
  unfold stage1WorkingAssn s1HalfDone s1ResEpDone s1CapTabDone s1RestZero
  dsimp only
  rw [hinit_frozen, hinit_hsign, hinit_hmag, hinit_flow, hinit_res]
  have hpure : (costLimbs.length = I.m ∧ adjPtrs.length = I.m ∧ adjLimbs.length = I.m ∧
      (List.replicate (2 * I.m) 0).length = 2 * I.m ∧
      (List.replicate (2 * I.m) 0).length = 2 * I.m ∧
      (List.replicate (2 * I.m) 0).length = 2 * I.m ∧
      (List.replicate 4 0).length = 4 ∧
      (List.replicate K_cap 0).length = K_cap ∧
      (List.replicate K_cap 0).length = K_cap ∧
      ∀ _ : Fin I.m, (List.replicate K_cap 0).length = K_cap) := by
    simp [hcol, hadjP, hadjL]
  rw [eq_true hpure, Assn.pure_true, mul_one]
  exact perm20

theorem stage1Start_meets {w : ℕ} {p : Program}
    {f hdrIdx halfIdx resEpIdx capTabIdx adjIdx : ℕ}
    (hp : p.procs[f]? = some (stage1Start hdrIdx halfIdx resEpIdx capTabIdx adjIdx))
    (hhdr : Meets w p hdrIdx ((stage1StartHdrSpec w).withCost fun x _ => stage1StartHdrCost x.1))
    (hhalf : Meets w p halfIdx ((stage1InitHalfCostsSpec w).withCost fun x _ => 40 * x.1.m + 80))
    (hrep : Meets w p resEpIdx ((stage1InitResEndpointsSpec w).withCost fun x _ => 75 * x.1.m + 140))
    (hct : Meets w p capTabIdx ((stage1InitCapTablesSpec w).withCost fun x _ =>
      120 * x.1.m + 17 * x.1.m * (bitScalingPhases x.1 / x.2.1 + 2) + 160))
    (hadj : Meets w p adjIdx ((stage1InitAdjCostsSpec w).withCost fun x _ =>
      100 * x.1.m + 55 * x.1.m * (costScaleBits x.1 / x.2.1 + 2) + 80)) :
    Meets w p f ((stage1StartSpec w).withCost fun x _ => stage1StartCost x.1 x.2.1) := by
  sep_enter ⟨I, k, capPtrs, capLimbs, costPtrs, costLimbs⟩
    with hm_pos hcp hcl hcop_l hcol hcapSpec hcostSpec hk h2k h2mk h6m hn1 huc hnr hsp
  set K_cap := bitScalingPhases I / k + 2
  set lay := mkStage1Layout h I.n I.m K_cap
  have hsum_cost : (costLimbs.map List.length).sum ≤ I.m * (costScaleBits I / k + 2) :=
    costLimbs_sum_length_le hk hcol (fun j hj => ⟨(hcostSpec j hj).1, (hcostSpec j hj).2.2⟩)
  have hKcap_bound : 2 * K_cap ≤ 2 * (I.m * K_cap) := by
    have h1 : K_cap ≤ I.m * K_cap := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right K_cap hm_pos
    omega
  have hAfter_le : h + 37 + I.n + 18 * I.m + 3 * I.m * K_cap + 2 * K_cap +
      (costLimbs.map List.length).sum ≤ h + stage1StartSpace I k := by
    unfold stage1StartSpace
    dsimp only [K_cap] at hsum_cost hKcap_bound ⊢
    have h3 : 3 * I.m * (bitScalingPhases I / k + 2) = 3 * (I.m * (bitScalingPhases I / k + 2)) :=
      Nat.mul_assoc _ _ _
    have h5 : 5 * I.m * (bitScalingPhases I / k + 2) = 5 * (I.m * (bitScalingPhases I / k + 2)) :=
      Nat.mul_assoc _ _ _
    omega
  have hpCapBuf_fit : lay.pCapBuf + I.m * K_cap < 2 ^ w := by
    dsimp only [lay, mkStage1Layout]; have : 3 * I.m * K_cap = 3 * (I.m * K_cap) := Nat.mul_assoc _ _ _
    omega
  have hpFlow_fit : lay.pFlow + I.m * K_cap < 2 ^ w := by
    dsimp only [lay, mkStage1Layout]; have : 3 * I.m * K_cap = 3 * (I.m * K_cap) := Nat.mul_assoc _ _ _
    omega
  have hpResFwd_fit : lay.pResFwdBuf + I.m * K_cap < 2 ^ w := by
    dsimp only [lay, mkStage1Layout]
    have : 2 * I.m * K_cap = 2 * (I.m * K_cap) := Nat.mul_assoc _ _ _
    have : 3 * I.m * K_cap = 3 * (I.m * K_cap) := Nat.mul_assoc _ _ _
    omega
  have hpResTail_fit : lay.pResTail + I.m < 2 ^ w := by dsimp only [lay, mkStage1Layout]; omega
  have hpResHead_fit : lay.pResHead + I.m < 2 ^ w := by dsimp only [lay, mkStage1Layout]; omega
  have hpResCapPtrs_fit : lay.pResCapPtrs + I.m < 2 ^ w := by dsimp only [lay, mkStage1Layout]; omega
  have hw1 : 1 < 2 ^ w := by
    have h2b := two_le_pow hk
    have h2bw := pow_lt_pow_w hk h2k
    omega
  have hcapSpec' : ∀ j (hj : j < I.m), CanonicalLimbs k (capLimbs.getD j []) ∧
      Nat.ofDigits (2 ^ k) (capLimbs.getD j []) = I.capacity ⟨j, hj⟩ :=
    fun j hj => ⟨(hcapSpec j hj).1, (hcapSpec j hj).2.2⟩
  have hcostSpec' : ∀ j (hj : j < I.m), CanonicalLimbs k (costLimbs.getD j []) ∧
      Nat.ofDigits (2 ^ k) (costLimbs.getD j []) = (I.cost ⟨j, hj⟩).natAbs :=
    fun j hj => ⟨(hcostSpec j hj).1, (hcostSpec j hj).2.2⟩
  sep_step from (I, k, capPtrs, capLimbs, costPtrs, costLimbs)
  let ptrs : Stage1HdrPtrs :=
    ⟨pIn, pTail_1, pHead_1, pCapPtrs_1, pCapLens_1, pCostSign_1, pCostPtrs_1, pCostLens_1⟩
  have hhAfter_eq : hAfter = h + 37 + I.n + 18 * I.m + 3 * I.m * K_cap + 2 * K_cap := by assumption
  sep_apply stage1StartInit_free_split (w := w) (n := I.n) (m := I.m) (K_cap := K_cap) (by omega)
  have hfree_eq : Assn.free (h + 37 + I.n + 18 * I.m + 3 * I.m * K_cap + 2 * K_cap)
      (2 ^ w - (h + 37 + I.n + 18 * I.m + 3 * I.m * K_cap + 2 * K_cap)) =
      Assn.free hAfter (2 ^ w - hAfter) := by rw [← hhAfter_eq]
  sep_apply hfree_eq
  sep_apply s1In_split I k capPtrs capLimbs costPtrs costLimbs
  sep_apply s1CapsHdr_fold I k lay ptrs
  -- 1. Half-costs
  sep_step from (I, k, lay, ptrs)
  sep_apply s1HalfDone_eq I lay
  -- 2. Residual endpoints
  sep_apply s1ResEpZero_eq lay I.m
  sep_step from (I, k, lay, ptrs)
  sep_apply s1ResEpDone_eq I lay
  -- 3. Capacity tables
  sep_apply s1InCap_eq I capPtrs capLimbs pCapPtrs_1 pCapLens_1
  sep_apply s1CapTabZero_eq lay I.m K_cap
  sep_step from (I, k, capPtrs, capLimbs, lay, ptrs)
  sep_apply (s1InCap_eq I capPtrs capLimbs pCapPtrs_1 pCapLens_1).symm
  sep_apply s1CapTabDone_eq I k lay capLimbs
  -- 4. Adjusted negative-cost limbs
  sep_apply s1InCost_eq I costPtrs costLimbs pCostPtrs_1 pCostLens_1
  sep_step from (I, k, costPtrs, costLimbs, lay, ptrs)
  have hadjP : adjPtrs.length = I.m := by assumption
  have hadjL : adjLimbs.length = I.m := by assumption
  sep_apply (s1InCost_eq I costPtrs costLimbs pCostPtrs_1 pCostLens_1).symm
  sep_apply (s1CapsHdr_fold I k lay ptrs).symm
  sep_apply (s1In_split I k capPtrs capLimbs costPtrs costLimbs pIn pTail_1 pHead_1 pCapPtrs_1
    pCapLens_1 pCostSign_1 pCostPtrs_1 pCostLens_1).symm
  sep_apply stage1Start_fold_work I k lay pCostSign_1 pCostLens_1 capLimbs costLimbs adjPtrs adjLimbs
    hcol hadjP hadjL
  unfold stage1StartCost
  sep_run

theorem stage1Start_meetsO {w : ℕ} {p : Program}
    {f hdrIdx halfIdx resEpIdx capTabIdx adjIdx : ℕ}
    (hp : p.procs[f]? = some (stage1Start hdrIdx halfIdx resEpIdx capTabIdx adjIdx))
    (hhdr : Meets w p hdrIdx ((stage1StartHdrSpec w).withCost fun x _ => stage1StartHdrCost x.1))
    (hhalf : Meets w p halfIdx ((stage1InitHalfCostsSpec w).withCost fun x _ => 40 * x.1.m + 80))
    (hrep : Meets w p resEpIdx ((stage1InitResEndpointsSpec w).withCost fun x _ => 75 * x.1.m + 140))
    (hct : Meets w p capTabIdx ((stage1InitCapTablesSpec w).withCost fun x _ =>
      120 * x.1.m + 17 * x.1.m * (bitScalingPhases x.1 / x.2.1 + 2) + 160))
    (hadj : Meets w p adjIdx ((stage1InitAdjCostsSpec w).withCost fun x _ =>
      100 * x.1.m + 55 * x.1.m * (costScaleBits x.1 / x.2.1 + 2) + 80)) :
    MeetsO w p f (stage1StartSpec w) fun x _ =>
      x.1.m * (bitScalingPhases x.1 / x.2.1 + costScaleBits x.1 / x.2.1 + 1) +
        bitScalingPhases x.1 + costScaleBits x.1 + 1 :=
  MeetsO.of_meets (stage1Start_meets hp hhdr hhalf hrep hct hadj) ⟨1500, fun x => by
    unfold stage1StartCost stage1StartHdrCost
    dsimp only
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
    omega⟩

/-- Complete polymorphic startup module bundling all Stage 1 initialization procedures. -/
def stage1StartMod {ι : Type}
    (startName hdrName metaName layoutName halfName resEpName capTabName adjName
      compName decName prepName padName fillPtrsName w8Name w9Name
      topName clogName blName copyName : ι) : Module ι :=
  ⟨[(compName, fun _ => stage1Compress),
    (decName, fun _ => stage1DecLimbs),
    (prepName, fun idx => stage1PrepNegCosts (idx decName) (idx copyName)),
    (padName, fun idx => stage1PadCaps (idx copyName)),
    (fillPtrsName, fun _ => stage1FillPtrs),
    (w8Name, fun _ => stage1Write8),
    (w9Name, fun _ => stage1Write9),
    (metaName, fun idx => stage1StartMeta (idx topName) (idx clogName) (idx blName)),
    (layoutName, fun idx => stage1WriteLayout (idx w8Name) (idx w9Name)),
    (hdrName, fun idx => stage1StartHdr (idx compName) (idx metaName) (idx layoutName)),
    (halfName, fun idx => stage1InitHalfCosts (idx copyName)),
    (resEpName, fun idx => stage1InitResEndpoints (idx copyName)),
    (capTabName, fun idx => stage1InitCapTables (idx padName) (idx fillPtrsName)),
    (adjName, fun idx => stage1InitAdjCosts (idx prepName)),
    (startName, fun idx => stage1Start (idx hdrName) (idx halfName) (idx resEpName)
      (idx capTabName) (idx adjName))]⟩

theorem stage1StartMod_noRand {ι : Type}
    (startName hdrName metaName layoutName halfName resEpName capTabName adjName
      compName decName prepName padName fillPtrsName w8Name w9Name
      topName clogName blName copyName : ι) :
    (stage1StartMod startName hdrName metaName layoutName halfName resEpName capTabName adjName
      compName decName prepName padName fillPtrsName w8Name w9Name
      topName clogName blName copyName).NoRand := by
  wram_no_rand

end MinCostFlow.NarrowProg.Stage1
