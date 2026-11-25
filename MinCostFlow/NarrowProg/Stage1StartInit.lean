module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import WordRAM.Std.Array
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1StartHelpers
public import MinCostFlow.NarrowProg.Stage1Layout
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Stage 1 startup initialization helpers (`Stage1StartInit`)

Four small, low-register initialization procedures invoked by `stage1Start`:
1. `stage1InitHalfCosts`: copies initial half-cost signs and magnitudes (`pCostSign -> pHSign, pHMag`).
2. `stage1InitResEndpoints`: copies the `2 * m` residual endpoints (`pCompTail, pCompHead -> pResTail, pResHead`).
3. `stage1InitCapTables`: pads capacities into `pCapBuf` and fills `pResCapPtrs`.
4. `stage1InitAdjCosts`: precomputes adjusted negative-cost limbs at `hAfter`, returning `curH`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow
  MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate

/-- Fixed input descriptor pointers threaded through the startup helpers. -/
structure Stage1HdrPtrs where
  pIn : ℕ
  pTail : ℕ
  pHead : ℕ
  pCapPtrs : ℕ
  pCapLens : ℕ
  pCostSign : ℕ
  pCostPtrs : ℕ
  pCostLens : ℕ

/-- Bundled descriptor headers `(pIn, lay.pCtx, lay.pResIn)` preserved read-only by all startup
initialization helpers. -/
def s1CapsHdr (I : Circulation) (k : ℕ) (lay : Stage1Layout) (ptrs : Stage1HdrPtrs) : Assn :=
  Assn.list ptrs.pIn [I.n, I.m, k, ptrs.pTail, ptrs.pHead, ptrs.pCapPtrs, ptrs.pCapLens,
    ptrs.pCostSign, ptrs.pCostPtrs, ptrs.pCostLens] *
  Assn.list lay.pCtx (stage1CtxWords I k lay ptrs.pCostSign ptrs.pCostLens) *
  Assn.list lay.pResIn
    [I.compress.n, 2 * I.m, k, lay.pResTail, lay.pResHead, lay.pResCSign, lay.pResCMag,
     lay.pResCapPtrs, lay.pResCapLens]

/-- Split `lay.pCtx` into three 8-word chunks inside `s1CapsHdr` so every header load has index `< 8`. -/
theorem s1CapsHdr_split (I : Circulation) (k : ℕ) (lay : Stage1Layout) (ptrs : Stage1HdrPtrs) :
    s1CapsHdr I k lay ptrs =
      Assn.list ptrs.pIn [I.n, I.m, k, ptrs.pTail, ptrs.pHead, ptrs.pCapPtrs, ptrs.pCapLens,
        ptrs.pCostSign, ptrs.pCostPtrs, ptrs.pCostLens] *
      Assn.list lay.pCtx [I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I,
        bitScalingPhases I / k + 2, lowerClip I.m, upperClip I.m] *
      Assn.list (lay.pCtx + 8) [freezeThreshold I.m, narrowCostRounds I.compress,
        lay.pCompTail, lay.pCompHead, ptrs.pCostSign, ptrs.pCostLens, lay.pAdjCostPtrs, lay.pCapBuf] *
      Assn.list (lay.pCtx + 16) [lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
        lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn] *
      Assn.list lay.pResIn
        [I.compress.n, 2 * I.m, k, lay.pResTail, lay.pResHead, lay.pResCSign, lay.pResCMag,
         lay.pResCapPtrs, lay.pResCapLens] := by
  unfold s1CapsHdr
  let c0 := [I.compress.n, I.m, k, costScaleBits I, bitScalingPhases I,
    bitScalingPhases I / k + 2, lowerClip I.m, upperClip I.m]
  let c1 := [freezeThreshold I.m, narrowCostRounds I.compress,
    lay.pCompTail, lay.pCompHead, ptrs.pCostSign, ptrs.pCostLens, lay.pAdjCostPtrs, lay.pCapBuf]
  let c2 := [lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
    lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn]
  have h1 := Assn.list_append lay.pCtx c0 c1
  have h2 := Assn.list_append lay.pCtx (c0 ++ c1) c2
  simp only [c0, c1, List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd] at h1 h2
  have hctx : Assn.list lay.pCtx (stage1CtxWords I k lay ptrs.pCostSign ptrs.pCostLens) =
      Assn.list lay.pCtx c0 * Assn.list (lay.pCtx + 8) c1 * Assn.list (lay.pCtx + 16) c2 := by
    rw [← h1, ← h2]; rfl
  rw [hctx]; dsimp only [c0, c1, c2]; simp only [mul_assoc]

/-- Helper bounding total limb lengths of `costLimbs` by `I.m * (costScaleBits I / k + 2)`. -/
theorem costLimbs_sum_length_le {I : Circulation} {k : ℕ} (hk : 1 ≤ k)
    {costLimbs : List (List ℕ)} (hlen : costLimbs.length = I.m)
    (hspec : ∀ j (hj : j < I.m), CanonicalLimbs k (costLimbs.getD j []) ∧
      Nat.ofDigits (2 ^ k) (costLimbs.getD j []) = (I.cost ⟨j, hj⟩).natAbs) :
    (costLimbs.map List.length).sum ≤ I.m * (costScaleBits I / k + 2) := by
  have hmax : ∀ l ∈ costLimbs, l.length ≤ costScaleBits I / k + 2 := by
    intro l hl
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    have hj' : j < I.m := by omega
    obtain ⟨hC, hval⟩ := hspec j hj'
    rw [List.getD_eq_getElem _ _ hj] at hC hval
    have hlt : Nat.ofDigits (2 ^ k) costLimbs[j] < 2 ^ costScaleBits I := by
      rw [hval]
      exact lt_of_le_of_lt
        (Finset.le_sup (f := fun e : Fin I.m => (I.cost e).natAbs) (Finset.mem_univ (Fin.mk j hj')))
        (Nat.lt_size_self (circMaxCost I))
    exact canonical_length_le_div_add_two hk hC hlt
  have hsum : ∀ ls : List (List ℕ), (∀ l ∈ ls, l.length ≤ costScaleBits I / k + 2) →
      (ls.map List.length).sum ≤ ls.length * (costScaleBits I / k + 2) := by
    intro ls hls
    induction ls with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have hx := hls x List.mem_cons_self
      have hxs := ih fun y hy => hls y (List.mem_cons_of_mem _ hy)
      omega
  simpa [hlen] using hsum costLimbs hmax

/-! ### 1. Initial half-costs (`stage1InitHalfCosts`) -/

/-- Copy initial half-cost signs and magnitudes (`pCostSign -> pHSign, pHMag`). -/
wram_def stage1InitHalfCosts (copyIdx : ℕ) (pIn, pCtx) {
  m := mem[pIn + 1]
  pCostSign := mem[pIn + 7]
  pHSign := mem[pCtx + 21]
  pHMag := mem[pCtx + 22]
  r := copyIdx(pCostSign, pHSign, m)
  r := copyIdx(pCostSign, pHMag, m)
  return 0
}

def stage1InitHalfCostsSpec (w : ℕ) : Spec (Circulation × ℕ × Stage1Layout × Stage1HdrPtrs) where
  pre := fun (I, k, lay, ptrs) args =>
    ⌜args = [ptrs.pIn, lay.pCtx] ∧ 1 < 2 ^ w⌝ *
    s1CapsHdr I k lay ptrs *
    Assn.list ptrs.pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
    Assn.list lay.pHSign (List.replicate I.m 0) *
    Assn.list lay.pHMag (List.replicate I.m 0)
  post := fun (I, k, lay, ptrs) args v =>
    ⌜args = [ptrs.pIn, lay.pCtx] ∧ v = 0⌝ *
    s1CapsHdr I k lay ptrs *
    Assn.list ptrs.pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
    Assn.list lay.pHSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
    Assn.list lay.pHMag (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0)

private def s1HalfBody (I : Circulation) (lay : Stage1Layout) (pCostSign : ℕ) : Assn :=
  Assn.list pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
  Assn.list lay.pHSign (List.replicate I.m 0) *
  Assn.list lay.pHMag (List.replicate I.m 0)

private theorem s1HalfBody_eq (I : Circulation) (lay : Stage1Layout) (pCostSign : ℕ) :
    Assn.list pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
    Assn.list lay.pHSign (List.replicate I.m 0) *
    Assn.list lay.pHMag (List.replicate I.m 0) = s1HalfBody I lay pCostSign := rfl

theorem stage1InitHalfCosts_meets {w : ℕ} {p : Program} {f copyIdx : ℕ}
    (hp : p.procs[f]? = some (stage1InitHalfCosts copyIdx))
    (hcopy : Meets w p copyIdx ((copySpec w).withCost fun x _ => 17 * x.1.length + 10)) :
    Meets w p f ((stage1InitHalfCostsSpec w).withCost fun x _ => 40 * x.1.m + 80) := by
  sep_enter ⟨I, k, lay, ptrs⟩ with hw1
  sep_apply s1HalfBody_eq I lay ptrs.pCostSign
  sep_apply s1CapsHdr_split I k lay ptrs
  iterate 4 sep_step
  subst m pCostSign pHSign pHMag
  sep_apply (s1CapsHdr_split I k lay ptrs).symm
  sep_apply (s1HalfBody_eq I lay ptrs.pCostSign).symm
  sep_step from (List.ofFn (fun e : Fin I.m => if I.cost e < 0 then 1 else 0), List.replicate I.m 0)
  sep_step from (List.ofFn (fun e : Fin I.m => if I.cost e < 0 then 1 else 0), List.replicate I.m 0)
  sep_run

/-! ### 2. Residual endpoints (`stage1InitResEndpoints`) -/

/-- Copy the `2 * m` residual endpoints (`pCompTail, pCompHead -> pResTail, pResHead`). -/
wram_def stage1InitResEndpoints (copyIdx : ℕ) (pCtx) {
  m := mem[pCtx + 1]
  pCompTail := mem[pCtx + 10]
  pCompHead := mem[pCtx + 11]
  pResIn := mem[pCtx + 23]
  pResTail := mem[pResIn + 3]
  pResHead := mem[pResIn + 4]
  r := copyIdx(pCompTail, pResTail, m)
  r := copyIdx(pCompHead, pResTail + m, m)
  r := copyIdx(pCompHead, pResHead, m)
  r := copyIdx(pCompTail, pResHead + m, m)
  return 0
}

def stage1InitResEndpointsSpec (w : ℕ) : Spec (Circulation × ℕ × Stage1Layout × Stage1HdrPtrs) where
  pre := fun (I, k, lay, ptrs) args =>
    let C := I.compress
    ⌜args = [lay.pCtx] ∧ 1 < 2 ^ w ∧
      lay.pResTail + I.m < 2 ^ w ∧ lay.pResHead + I.m < 2 ^ w⌝ *
    s1CapsHdr I k lay ptrs *
    Assn.list lay.pCompTail (List.ofFn fun e : Fin I.m => (C.tail e).val) *
    Assn.list lay.pCompHead (List.ofFn fun e : Fin I.m => (C.head e).val) *
    Assn.list lay.pResTail (List.replicate I.m 0) *
    Assn.list (lay.pResTail + I.m) (List.replicate I.m 0) *
    Assn.list lay.pResHead (List.replicate I.m 0) *
    Assn.list (lay.pResHead + I.m) (List.replicate I.m 0)
  post := fun (I, k, lay, ptrs) args v =>
    let C := I.compress
    ⌜args = [lay.pCtx] ∧ v = 0⌝ *
    s1CapsHdr I k lay ptrs *
    Assn.list lay.pCompTail (List.ofFn fun e : Fin I.m => (C.tail e).val) *
    Assn.list lay.pCompHead (List.ofFn fun e : Fin I.m => (C.head e).val) *
    Assn.list lay.pResTail
      ((List.ofFn fun e : Fin I.m => (C.tail e).val) ++
       (List.ofFn fun e : Fin I.m => (C.head e).val)) *
    Assn.list lay.pResHead
      ((List.ofFn fun e : Fin I.m => (C.head e).val) ++
       (List.ofFn fun e : Fin I.m => (C.tail e).val))

private def s1ResEpBody (I : Circulation) (lay : Stage1Layout) : Assn :=
  Assn.list lay.pCompTail (List.ofFn fun e : Fin I.m => (I.compress.tail e).val) *
  Assn.list lay.pCompHead (List.ofFn fun e : Fin I.m => (I.compress.head e).val) *
  Assn.list lay.pResTail (List.replicate I.m 0) *
  Assn.list (lay.pResTail + I.m) (List.replicate I.m 0) *
  Assn.list lay.pResHead (List.replicate I.m 0) *
  Assn.list (lay.pResHead + I.m) (List.replicate I.m 0)

private theorem s1ResEpBody_eq (I : Circulation) (lay : Stage1Layout) :
    Assn.list lay.pCompTail (List.ofFn fun e : Fin I.m => (I.compress.tail e).val) *
    Assn.list lay.pCompHead (List.ofFn fun e : Fin I.m => (I.compress.head e).val) *
    Assn.list lay.pResTail (List.replicate I.m 0) *
    Assn.list (lay.pResTail + I.m) (List.replicate I.m 0) *
    Assn.list lay.pResHead (List.replicate I.m 0) *
    Assn.list (lay.pResHead + I.m) (List.replicate I.m 0) = s1ResEpBody I lay := rfl

theorem stage1InitResEndpoints_meets {w : ℕ} {p : Program} {f copyIdx : ℕ}
    (hp : p.procs[f]? = some (stage1InitResEndpoints copyIdx))
    (hcopy : Meets w p copyIdx ((copySpec w).withCost fun x _ => 17 * x.1.length + 10)) :
    Meets w p f ((stage1InitResEndpointsSpec w).withCost fun x _ => 75 * x.1.m + 140) := by
  sep_enter ⟨I, k, lay, ptrs⟩ with hw1 hrt hrh
  sep_apply s1ResEpBody_eq I lay
  sep_apply s1CapsHdr_split I k lay ptrs
  iterate 4 sep_step
  subst m pCompTail pCompHead pResIn
  iterate 2 sep_step
  subst pResTail pResHead
  sep_apply (s1CapsHdr_split I k lay ptrs).symm
  sep_apply (s1ResEpBody_eq I lay).symm
  sep_step from (List.ofFn (fun e : Fin I.m => (I.compress.tail e).val), List.replicate I.m 0)
  sep_step from (List.ofFn (fun e : Fin I.m => (I.compress.head e).val), List.replicate I.m 0)
  sep_step from (List.ofFn (fun e : Fin I.m => (I.compress.head e).val), List.replicate I.m 0)
  sep_step from (List.ofFn (fun e : Fin I.m => (I.compress.tail e).val), List.replicate I.m 0)
  have hm_t : Assn.list lay.pResTail (List.ofFn fun e : Fin I.m => (I.compress.tail e).val) *
      Assn.list (lay.pResTail + I.m) (List.ofFn fun e : Fin I.m => (I.compress.head e).val) =
      Assn.list lay.pResTail ((List.ofFn fun e : Fin I.m => (I.compress.tail e).val) ++
        (List.ofFn fun e : Fin I.m => (I.compress.head e).val)) := by rw [Assn.list_append, List.length_ofFn]
  have hm_h : Assn.list lay.pResHead (List.ofFn fun e : Fin I.m => (I.compress.head e).val) *
      Assn.list (lay.pResHead + I.m) (List.ofFn fun e : Fin I.m => (I.compress.tail e).val) =
      Assn.list lay.pResHead ((List.ofFn fun e : Fin I.m => (I.compress.head e).val) ++
        (List.ofFn fun e : Fin I.m => (I.compress.tail e).val)) := by rw [Assn.list_append, List.length_ofFn]
  sep_apply hm_t; sep_apply hm_h
  sep_run

/-! ### 3. Padded capacities & residual capacity pointers (`stage1InitCapTables`) -/

/-- Pad input capacities into `pCapBuf` and fill `pResCapPtrs` for forward/reverse residual edges. -/
wram_def stage1InitCapTables (padIdx fillPtrsIdx : ℕ) (pIn, pCtx) {
  m := mem[pIn + 1]
  pCapPtrs := mem[pIn + 5]
  pCapLens := mem[pIn + 6]
  Kcap := mem[pCtx + 5]
  pCapBuf := mem[pCtx + 15]
  pFlow := mem[pCtx + 16]
  pResFwdBuf := mem[pCtx + 17]
  pResIn := mem[pCtx + 23]
  pResCapPtrs := mem[pResIn + 7]
  r := padIdx(m, Kcap, pCapPtrs, pCapLens, pCapBuf)
  r := fillPtrsIdx(m, Kcap, pResFwdBuf, pResCapPtrs)
  r := fillPtrsIdx(m, Kcap, pFlow, pResCapPtrs + m)
  return 0
}

def stage1InitCapTablesSpec (w : ℕ) :
    Spec (Circulation × ℕ × List ℕ × List (List ℕ) × Stage1Layout × Stage1HdrPtrs) where
  pre := fun (I, k, capPtrs, capLimbs, lay, ptrs) args =>
    let K_cap := bitScalingPhases I / k + 2
    ⌜args = [ptrs.pIn, lay.pCtx] ∧
      capPtrs.length = I.m ∧ capLimbs.length = I.m ∧
      (∀ j (hj : j < I.m), CanonicalLimbs k (capLimbs.getD j []) ∧
        Nat.ofDigits (2 ^ k) (capLimbs.getD j []) = I.capacity ⟨j, hj⟩) ∧
      1 ≤ k ∧ 2 * k ≤ w ∧
      lay.pCapBuf + I.m * K_cap < 2 ^ w ∧
      lay.pFlow + I.m * K_cap < 2 ^ w ∧
      lay.pResFwdBuf + I.m * K_cap < 2 ^ w ∧
      lay.pResCapPtrs + I.m < 2 ^ w⌝ *
    s1CapsHdr I k lay ptrs *
    Assn.list ptrs.pCapPtrs capPtrs *
    Assn.list ptrs.pCapLens (capLimbs.map List.length) *
    (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
    Assn.list lay.pResCapPtrs (List.replicate I.m 0) *
    Assn.list (lay.pResCapPtrs + I.m) (List.replicate I.m 0) *
    (∏ j ∈ Finset.range I.m, Assn.list (lay.pCapBuf + j * K_cap) (List.replicate K_cap 0))
  post := fun (I, k, capPtrs, capLimbs, lay, ptrs) args v =>
    let K_cap := bitScalingPhases I / k + 2
    ⌜args = [ptrs.pIn, lay.pCtx] ∧ v = 0⌝ *
    s1CapsHdr I k lay ptrs *
    Assn.list ptrs.pCapPtrs capPtrs *
    Assn.list ptrs.pCapLens (capLimbs.map List.length) *
    (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
    Assn.list lay.pResCapPtrs
      ((List.ofFn fun e : Fin I.m => lay.pResFwdBuf + e.val * K_cap) ++
       (List.ofFn fun e : Fin I.m => lay.pFlow + e.val * K_cap)) *
    (∏ j ∈ Finset.range I.m, Assn.list (lay.pCapBuf + j * K_cap)
      (padLimbs K_cap (capLimbs.getD j [])))

private def s1CapTabBody (I : Circulation) (k : ℕ) (lay : Stage1Layout) (ptrs : Stage1HdrPtrs)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ)) : Assn :=
  Assn.list ptrs.pCapPtrs capPtrs *
  Assn.list ptrs.pCapLens (capLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
  Assn.list lay.pResCapPtrs (List.replicate I.m 0) *
  Assn.list (lay.pResCapPtrs + I.m) (List.replicate I.m 0) *
  (∏ j ∈ Finset.range I.m, Assn.list (lay.pCapBuf + j * (bitScalingPhases I / k + 2))
    (List.replicate (bitScalingPhases I / k + 2) 0))

private theorem s1CapTabBody_eq (I : Circulation) (k : ℕ) (lay : Stage1Layout) (ptrs : Stage1HdrPtrs)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ)) :
    Assn.list ptrs.pCapPtrs capPtrs *
    Assn.list ptrs.pCapLens (capLimbs.map List.length) *
    (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
    Assn.list lay.pResCapPtrs (List.replicate I.m 0) *
    Assn.list (lay.pResCapPtrs + I.m) (List.replicate I.m 0) *
    (∏ j ∈ Finset.range I.m, Assn.list (lay.pCapBuf + j * (bitScalingPhases I / k + 2))
      (List.replicate (bitScalingPhases I / k + 2) 0)) =
    s1CapTabBody I k lay ptrs capPtrs capLimbs := rfl

theorem stage1InitCapTables_meets {w : ℕ} {p : Program} {f padIdx fillPtrsIdx : ℕ}
    (hp : p.procs[f]? = some (stage1InitCapTables padIdx fillPtrsIdx))
    (hpad : Meets w p padIdx ((stage1PadCapsSpec w).withCost fun x _ => 50 * x.1 + 17 * x.1 * x.2.1 + 20))
    (hfill : Meets w p fillPtrsIdx ((stage1FillPtrsSpec w).withCost fun x _ => 30 * x.1 + 20)) :
    Meets w p f ((stage1InitCapTablesSpec w).withCost fun x _ =>
      120 * x.1.m + 17 * x.1.m * (bitScalingPhases x.1 / x.2.1 + 2) + 160) := by
  sep_enter ⟨I, k, capPtrs, capLimbs, lay, ptrs⟩
    with hcp hcl hcapSpec hk h2k hpCapBuf_fit hpFlow_fit hpResFwd_fit hpResCapPtrs_fit
  set T_U := bitScalingPhases I
  set K_cap := T_U / k + 2
  have h2b : 2 ≤ 2 ^ k := two_le_pow hk
  have h2bw : 2 ^ k + 2 ^ k ≤ 2 ^ w := pow_lt_pow_w hk h2k
  have hcap_len_le : ∀ j < I.m, (capLimbs.getD j []).length ≤ K_cap := by
    intro j hj
    obtain ⟨hCj, hvalj⟩ := hcapSpec j hj
    have hlt : Nat.ofDigits (2 ^ k) (capLimbs.getD j []) < 2 ^ T_U := by
      rw [hvalj]
      exact lt_of_le_of_lt
        (Finset.le_sup (f := I.capacity) (Finset.mem_univ (Fin.mk j hj)))
        (Nat.lt_size_self (circMaxCapacity I))
    exact canonical_length_le_div_add_two hk hCj hlt
  sep_apply s1CapTabBody_eq I k lay ptrs capPtrs capLimbs
  sep_apply s1CapsHdr_split I k lay ptrs
  iterate 8 sep_step
  subst m pCapPtrs pCapLens Kcap pCapBuf pFlow pResFwdBuf pResIn
  sep_step
  subst pResCapPtrs
  sep_apply (s1CapsHdr_split I k lay ptrs).symm
  sep_apply (s1CapTabBody_eq I k lay ptrs capPtrs capLimbs).symm
  sep_step from (I.m, K_cap, capPtrs, capLimbs)
  sep_step from (I.m, K_cap, lay.pResFwdBuf)
  sep_step from (I.m, K_cap, lay.pFlow)
  have hm_p : Assn.list lay.pResCapPtrs (List.ofFn fun e : Fin I.m => lay.pResFwdBuf + e.val * K_cap) *
      Assn.list (lay.pResCapPtrs + I.m) (List.ofFn fun e : Fin I.m => lay.pFlow + e.val * K_cap) =
      Assn.list lay.pResCapPtrs ((List.ofFn fun e : Fin I.m => lay.pResFwdBuf + e.val * K_cap) ++
        (List.ofFn fun e : Fin I.m => lay.pFlow + e.val * K_cap)) := by rw [Assn.list_append, List.length_ofFn]
  sep_apply hm_p
  sep_run

/-! ### 4. Adjusted negative-cost limbs (`stage1InitAdjCosts`) -/

/-- Precompute adjusted negative-cost limbs starting at `hAfter`, returning `curH`. -/
wram_def stage1InitAdjCosts (prepIdx : ℕ) (pIn, pCtx, hAfter) {
  m := mem[pIn + 1]
  k := mem[pIn + 2]
  pCostSign := mem[pIn + 7]
  pCostPtrs := mem[pIn + 8]
  pCostLens := mem[pIn + 9]
  pAdjCostPtrs := mem[pCtx + 14]
  curH := prepIdx(m, k, pCostSign, pCostPtrs, pCostLens, pAdjCostPtrs, hAfter)
  return curH
}

def stage1InitAdjCostsSpec (w : ℕ) :
    Spec (Circulation × ℕ × List ℕ × List (List ℕ) × Stage1Layout × Stage1HdrPtrs) where
  pre := fun (I, k, costPtrs, costLimbs, lay, ptrs) args =>
    ⨆ (hAfter : ℕ),
      ⌜args = [ptrs.pIn, lay.pCtx, hAfter] ∧
        costPtrs.length = I.m ∧ costLimbs.length = I.m ∧
        (∀ j (hj : j < I.m), CanonicalLimbs k (costLimbs.getD j []) ∧
          Nat.ofDigits (2 ^ k) (costLimbs.getD j []) = (I.cost ⟨j, hj⟩).natAbs) ∧
        1 ≤ k ∧ 2 * k ≤ w ∧
        hAfter + (costLimbs.map List.length).sum < 2 ^ w⌝ *
      s1CapsHdr I k lay ptrs *
      Assn.list ptrs.pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
      Assn.list ptrs.pCostPtrs costPtrs *
      Assn.list ptrs.pCostLens (costLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])) *
      Assn.list lay.pAdjCostPtrs (List.replicate I.m 0) *
      Assn.free hAfter (2 ^ w - hAfter)
  post := fun (I, k, costPtrs, costLimbs, lay, ptrs) args h' =>
    ⨆ (hAfter : ℕ) (adjPtrs : List ℕ) (adjLimbs : List (List ℕ)),
      ⌜args = [ptrs.pIn, lay.pCtx, hAfter] ∧
        h' = hAfter + (costLimbs.map List.length).sum ∧
        adjPtrs.length = I.m ∧ adjLimbs.length = I.m ∧
        (∀ j (hj : j < I.m), Limbs k (adjLimbs.getD j []) ∧
          (adjLimbs.getD j []).length = (costLimbs.getD j []).length ∧
          Nat.ofDigits (2 ^ k) (adjLimbs.getD j []) =
            if I.cost ⟨j, hj⟩ < 0 then (I.cost ⟨j, hj⟩).natAbs - 1 else (I.cost ⟨j, hj⟩).natAbs)⌝ *
      s1CapsHdr I k lay ptrs *
      Assn.list ptrs.pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
      Assn.list ptrs.pCostPtrs costPtrs *
      Assn.list ptrs.pCostLens (costLimbs.map List.length) *
      (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])) *
      Assn.list lay.pAdjCostPtrs adjPtrs *
      (∏ j ∈ Finset.range I.m, Assn.list (adjPtrs.getD j 0) (adjLimbs.getD j [])) *
      Assn.free h' (2 ^ w - h')

private def s1AdjBody (w : ℕ) (I : Circulation) (lay : Stage1Layout) (ptrs : Stage1HdrPtrs)
    (costPtrs : List ℕ) (costLimbs : List (List ℕ)) (hAfter : ℕ) : Assn :=
  Assn.list ptrs.pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
  Assn.list ptrs.pCostPtrs costPtrs *
  Assn.list ptrs.pCostLens (costLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])) *
  Assn.list lay.pAdjCostPtrs (List.replicate I.m 0) *
  Assn.free hAfter (2 ^ w - hAfter)

private theorem s1AdjBody_eq (w : ℕ) (I : Circulation) (lay : Stage1Layout) (ptrs : Stage1HdrPtrs)
    (costPtrs : List ℕ) (costLimbs : List (List ℕ)) (hAfter : ℕ) :
    Assn.list ptrs.pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
    Assn.list ptrs.pCostPtrs costPtrs *
    Assn.list ptrs.pCostLens (costLimbs.map List.length) *
    (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j [])) *
    Assn.list lay.pAdjCostPtrs (List.replicate I.m 0) *
    Assn.free hAfter (2 ^ w - hAfter) =
    s1AdjBody w I lay ptrs costPtrs costLimbs hAfter := rfl

theorem stage1InitAdjCosts_meets {w : ℕ} {p : Program} {f prepIdx : ℕ}
    (hp : p.procs[f]? = some (stage1InitAdjCosts prepIdx))
    (hprep : Meets w p prepIdx ((stage1PrepNegCostsSpec w).withCost fun x _ =>
      95 * x.1.m + 55 * (x.2.2.2.1.map List.length).sum + 25)) :
    Meets w p f ((stage1InitAdjCostsSpec w).withCost fun x _ =>
      100 * x.1.m + 55 * x.1.m * (costScaleBits x.1 / x.2.1 + 2) + 80) := by
  sep_enter ⟨I, k, costPtrs, costLimbs, lay, ptrs⟩
    with hcop hcol hcostSpec hk h2k hcost_fit
  have h2b : 2 ≤ 2 ^ k := two_le_pow hk
  have h2bw : 2 ^ k + 2 ^ k ≤ 2 ^ w := pow_lt_pow_w hk h2k
  have hsum_cost : (costLimbs.map List.length).sum ≤ I.m * (costScaleBits I / k + 2) :=
    costLimbs_sum_length_le hk hcol hcostSpec
  have h55 : 55 * (costLimbs.map List.length).sum ≤ 55 * I.m * (costScaleBits I / k + 2) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 55 hsum_cost
  have hcostL : ∀ j (hj : j < I.m), Limbs k (costLimbs.getD j []) ∧
      Nat.ofDigits (2 ^ k) (costLimbs.getD j []) = (I.cost ⟨j, hj⟩).natAbs :=
    fun j hj => ⟨(hcostSpec j hj).1.1, (hcostSpec j hj).2⟩
  sep_apply s1AdjBody_eq w I lay ptrs costPtrs costLimbs hAfter
  sep_apply s1CapsHdr_split I k lay ptrs
  iterate 6 sep_step
  subst m k_1 pCostSign pCostPtrs pCostLens pAdjCostPtrs
  sep_apply (s1CapsHdr_split I k lay ptrs).symm
  sep_apply (s1AdjBody_eq w I lay ptrs costPtrs costLimbs hAfter).symm
  sep_step from (I, k, costPtrs, costLimbs, List.replicate I.m 0)
  sep_run

end MinCostFlow.NarrowProg.Stage1
