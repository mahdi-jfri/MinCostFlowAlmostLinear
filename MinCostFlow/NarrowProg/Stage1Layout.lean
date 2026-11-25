module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import WordRAM.Std.Array
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1StartHelpers
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Stage 1 working-memory layout and startup array helpers

This file defines:
- `stage1PadCaps`: copies canonical capacity limb lists into fixed-width `K_cap`-limb buffers.
- `stage1FillPtrs`: fills a strided pointer array `base + e * stride`.
- `Stage1Layout` and `mkStage1Layout`: the deterministic memory layout allocated at `h`.
- `stage1CtxWords` and `stage1WorkingAssn`: the persistent Stage 1 working-memory assertion
  carried across all `narrowCostRounds C` rounds.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow
  MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate

/-! ### 1. Padding capacities to fixed limb width (`stage1PadCaps`) -/

/-- Copy each canonical capacity limb list into its zero-padded `K_cap`-limb slot in `pCapBuf`. -/
wram_def stage1PadCaps (copyIdx : ℕ) (m, K_cap, pCapPtrs, pCapLens, pCapBuf) {
  dst := pCapBuf
  for e in 0 .. m {
    src := mem[pCapPtrs + e]
    len := mem[pCapLens + e]
    r := copyIdx(src, dst, len)
    dst := dst + K_cap
  }
  return 0
}

/-- Specification of `stage1PadCaps`. -/
def stage1PadCapsSpec (w : ℕ) : Spec (ℕ × ℕ × List ℕ × List (List ℕ)) where
  pre := fun (m, K_cap, capPtrs, capLimbs) args =>
    ⨆ (pCapPtrs : ℕ) (pCapLens : ℕ) (pCapBuf : ℕ),
      ⌜args = [m, K_cap, pCapPtrs, pCapLens, pCapBuf] ∧
        capPtrs.length = m ∧ capLimbs.length = m ∧
        (∀ j < m, (capLimbs.getD j []).length ≤ K_cap) ∧
        pCapBuf + m * K_cap < 2 ^ w ∧ 1 < 2 ^ w⌝ *
      Assn.list pCapPtrs capPtrs *
      Assn.list pCapLens (capLimbs.map List.length) *
      (∏ j ∈ Finset.range m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
      (∏ j ∈ Finset.range m, Assn.list (pCapBuf + j * K_cap) (List.replicate K_cap 0))
  post := fun (m, K_cap, capPtrs, capLimbs) args v =>
    ⨆ (pCapPtrs : ℕ) (pCapLens : ℕ) (pCapBuf : ℕ),
      ⌜args = [m, K_cap, pCapPtrs, pCapLens, pCapBuf] ∧ v = 0⌝ *
      Assn.list pCapPtrs capPtrs *
      Assn.list pCapLens (capLimbs.map List.length) *
      (∏ j ∈ Finset.range m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
      (∏ j ∈ Finset.range m, Assn.list (pCapBuf + j * K_cap) (padLimbs K_cap (capLimbs.getD j [])))

theorem stage1PadCaps_meets {w : ℕ} {p : Program} {f copyIdx : ℕ}
    (hp : p.procs[f]? = some (stage1PadCaps copyIdx))
    (hcopy : Meets w p copyIdx ((copySpec w).withCost fun x _ => 17 * x.1.length + 10)) :
    Meets w p f ((stage1PadCapsSpec w).withCost fun x _ =>
      50 * x.1 + 17 * x.1 * x.2.1 + 20) := by
  sep_enter ⟨m, K_cap, capPtrs, capLimbs⟩ with hcp hcl hlenLe hfit hw
  sep_step
  sep_for (fun e (tmp : ℕ × ℕ × ℕ) =>
    ⟨[m, K_cap, pCapPtrs, pCapLens, pCapBuf, pCapBuf + e * K_cap, e, tmp.1, tmp.2.1, tmp.2.2],
      e ≤ m, (40 + 17 * K_cap) * (m - e) + 5,
      [Assn.list pCapPtrs capPtrs,
       Assn.list pCapLens (capLimbs.map List.length),
       ∏ j ∈ Finset.range m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j []),
       ∏ j ∈ Finset.range m, Assn.list (pCapBuf + j * K_cap)
         (if j < e then padLimbs K_cap (capLimbs.getD j []) else List.replicate K_cap 0)]⟩) with ⟨src, len, r⟩
  · have hmem : e ∈ Finset.range m := Finset.mem_range.mpr hhi
    have hli : (capLimbs.getD e []).length ≤ K_cap := hlenLe e hhi
    have hlen_i : (capLimbs.map List.length)[e]'(by simp; omega) =
        (capLimbs.getD e []).length := by
      rw [List.getElem_map, List.getD_eq_getElem _ _ (by omega : e < capLimbs.length)]
    have hptr_i : capPtrs[e]'(by omega) = capPtrs.getD e 0 :=
      (List.getD_eq_getElem _ _ (by omega)).symm
    have hdst_next : pCapBuf + e * K_cap + K_cap = pCapBuf + (e + 1) * K_cap := by
      rw [Nat.succ_mul]; omega
    have hdst_next_lt : pCapBuf + (e + 1) * K_cap < 2 ^ w := by
      have : (e + 1) * K_cap ≤ m * K_cap := Nat.mul_le_mul_right K_cap (by omega)
      omega
    have hsplit_zero :
        Assn.list (pCapBuf + e * K_cap) (List.replicate K_cap 0) =
        Assn.list (pCapBuf + e * K_cap) (List.replicate (capLimbs.getD e []).length 0) *
        Assn.list (pCapBuf + e * K_cap + (capLimbs.getD e []).length)
          (List.replicate (K_cap - (capLimbs.getD e []).length) 0) := by
      have heq : List.replicate K_cap 0 =
          List.replicate (capLimbs.getD e []).length 0 ++
          List.replicate (K_cap - (capLimbs.getD e []).length) 0 := by
        rw [← List.replicate_add, Nat.add_sub_cancel' hli]
      rw [heq, Assn.list_append, List.length_replicate]
    sep_step; sep_step
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (capPtrs.getD j 0) (capLimbs.getD j []))
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pCapBuf + j * K_cap)
        (if j < e then padLimbs K_cap (capLimbs.getD j []) else List.replicate K_cap 0))
    have hnotlt : (if e < e then padLimbs K_cap (capLimbs.getD e []) else List.replicate K_cap 0) =
        List.replicate K_cap 0 := by simp
    rw [hnotlt]
    sep_apply hsplit_zero
    sep_step from (capLimbs.getD e [], List.replicate (capLimbs.getD e []).length 0)
    have hmerge_pad :
        Assn.list (pCapBuf + e * K_cap) (capLimbs.getD e []) *
        Assn.list (pCapBuf + e * K_cap + (capLimbs.getD e []).length)
          (List.replicate (K_cap - (capLimbs.getD e []).length) 0) =
        Assn.list (pCapBuf + e * K_cap) (padLimbs K_cap (capLimbs.getD e [])) := by
      rw [← Assn.list_append]; rfl
    sep_apply hmerge_pad
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (capPtrs.getD j 0) (capLimbs.getD j []))).symm
    have hprod_upd :
        Assn.list (pCapBuf + e * K_cap) (padLimbs K_cap (capLimbs.getD e [])) *
        (∏ j ∈ (Finset.range m).erase e, Assn.list (pCapBuf + j * K_cap)
          (if j < e then padLimbs K_cap (capLimbs.getD j []) else List.replicate K_cap 0)) =
        ∏ j ∈ Finset.range m, Assn.list (pCapBuf + j * K_cap)
          (if j < e + 1 then padLimbs K_cap (capLimbs.getD j []) else List.replicate K_cap 0) := by
      rw [Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (pCapBuf + j * K_cap)
          (if j < e + 1 then padLimbs K_cap (capLimbs.getD j []) else List.replicate K_cap 0))]
      simp only [Nat.lt_succ_self, ↓reduceIte]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      have hne : j ≠ e := (Finset.mem_erase.mp hj).1
      have hiff : (j < e) ↔ (j < e + 1) := by omega
      simp only [hiff]
    sep_apply hprod_upd
    have hcost_step : 17 * (capLimbs.getD e []).length + 10 ≤ 17 * K_cap + 10 := by
      have := Nat.mul_le_mul_left 17 hli; omega
    have hmul_sub : (40 + 17 * K_cap) * (m - e) =
        (40 + 17 * K_cap) + (40 + 17 * K_cap) * (m - (e + 1)) := by
      have : m - e = (m - (e + 1)) + 1 := by omega
      rw [this, Nat.mul_add, Nat.mul_one]; omega
    sep_run
  · have hprod_end :
        (∏ j ∈ Finset.range m, Assn.list (pCapBuf + j * K_cap)
          (if j < m then padLimbs K_cap (capLimbs.getD j []) else List.replicate K_cap 0)) =
        ∏ j ∈ Finset.range m, Assn.list (pCapBuf + j * K_cap) (padLimbs K_cap (capLimbs.getD j [])) :=
      Finset.prod_congr rfl fun j hj => by simp [Finset.mem_range.mp hj]
    rw [hprod_end]
    sep_run

theorem stage1PadCaps_meetsO {w : ℕ} {p : Program} {f copyIdx : ℕ}
    (hp : p.procs[f]? = some (stage1PadCaps copyIdx))
    (hcopy : Meets w p copyIdx ((copySpec w).withCost fun x _ => 17 * x.1.length + 10)) :
    MeetsO w p f (stage1PadCapsSpec w) fun x _ => x.1 * (x.2.1 + 1) + 1 :=
  MeetsO.of_meets (stage1PadCaps_meets hp hcopy) ⟨50, fun x => by dsimp only; nlinarith⟩

/-! ### 2. Filling a strided pointer table (`stage1FillPtrs`) -/

/-- Fill `m` entries at `dst` with `base + e * stride` for `e = 0, …, m - 1`. -/
wram_def stage1FillPtrs (m, stride, base, dst) {
  cur := base
  for e in 0 .. m {
    mem[dst + e] := cur
    cur := cur + stride
  }
  return 0
}

/-- Specification of `stage1FillPtrs`. -/
def stage1FillPtrsSpec (w : ℕ) : Spec (ℕ × ℕ × ℕ) where
  pre := fun (m, stride, base) args => ⨆ dst : ℕ,
    ⌜args = [m, stride, base, dst] ∧ base + m * stride < 2 ^ w ∧ 1 < 2 ^ w⌝ *
    Assn.list dst (List.replicate m 0)
  post := fun (m, stride, base) args v => ⨆ dst : ℕ,
    ⌜args = [m, stride, base, dst] ∧ v = 0⌝ *
    Assn.list dst (List.ofFn fun e : Fin m => base + e.val * stride)

theorem stage1FillPtrs_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1FillPtrs) :
    Meets w p f ((stage1FillPtrsSpec w).withCost fun x _ => 30 * x.1 + 20) := by
  sep_enter ⟨m, stride, base⟩ with hfit hw
  set ptrs := List.ofFn (fun e : Fin m => base + e.val * stride) with hptrs_def
  have hlen : ptrs.length = m := by simp [hptrs_def]
  sep_step
  sep_for (fun e =>
    ⟨[m, stride, base, dst, base + e * stride, e],
      e ≤ m, 20 * (m - e) + 5,
      [Assn.list dst (ptrs.take e ++ (List.replicate m 0).drop e)]⟩)
  · have hnext : base + e * stride + stride = base + (e + 1) * stride := by
      rw [Nat.succ_mul]; omega
    have hnext_lt : base + (e + 1) * stride < 2 ^ w := by
      have : (e + 1) * stride ≤ m * stride := Nat.mul_le_mul_right stride (by omega); omega
    have hpe : ptrs[e]'(by omega) = base + e * stride := by simp [hptrs_def]
    have hlen' : (ptrs.take e ++ (List.replicate m 0).drop e).length = m := by simp [hlen]; omega
    sep_run
    rw [← hpe]
    exact set_take_append_drop (by omega) (by simp [hlen]) rfl
  · rw [List.take_of_length_le (by omega), List.drop_of_length_le (by simp), List.append_nil]
    sep_run

theorem stage1FillPtrs_meetsO {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1FillPtrs) :
    MeetsO w p f (stage1FillPtrsSpec w) fun x _ => x.1 + 1 :=
  MeetsO.of_meets (stage1FillPtrs_meets hp) ⟨30, fun _ => by dsimp only; omega⟩

/-! ### 3. Persistent Stage 1 working-memory layout -/

/-- Deterministic memory layout allocated at `h` by `stage1Start` for `I` with limb width `k`. -/
structure Stage1Layout where
  pCtx : ℕ
  pResIn : ℕ
  pResOut : ℕ
  pCompTail : ℕ
  pCompHead : ℕ
  pAdjCostPtrs : ℕ
  pFrozen : ℕ
  pHSign : ℕ
  pHMag : ℕ
  pResTail : ℕ
  pResHead : ℕ
  pResCSign : ℕ
  pResCMag : ℕ
  pResCapPtrs : ℕ
  pResCapLens : ℕ
  pCapBuf : ℕ
  pFlow : ℕ
  pResFwdBuf : ℕ
  pTmp1 : ℕ
  pTmp2 : ℕ

/-- Construct the `Stage1Layout` allocated consecutively from heap base `h`. -/
def mkStage1Layout (h n m K_cap : ℕ) : Stage1Layout where
  pCtx := h
  pResIn := h + 24
  pResOut := h + 33
  pCompTail := h + 37 + n
  pCompHead := h + 37 + n + m
  pAdjCostPtrs := h + 37 + n + 2 * m
  pFrozen := h + 37 + n + 3 * m
  pHSign := h + 37 + n + 4 * m
  pHMag := h + 37 + n + 5 * m
  pResTail := h + 37 + n + 6 * m
  pResHead := h + 37 + n + 8 * m
  pResCSign := h + 37 + n + 10 * m
  pResCMag := h + 37 + n + 12 * m
  pResCapPtrs := h + 37 + n + 14 * m
  pResCapLens := h + 37 + n + 16 * m
  pCapBuf := h + 37 + n + 18 * m
  pFlow := h + 37 + n + 18 * m + m * K_cap
  pResFwdBuf := h + 37 + n + 18 * m + 2 * m * K_cap
  pTmp1 := h + 37 + n + 18 * m + 3 * m * K_cap
  pTmp2 := h + 37 + n + 18 * m + 3 * m * K_cap + K_cap

/-- The 24-word context header stored at `lay.pCtx`. -/
def stage1CtxWords (I : Circulation) (k : ℕ) (lay : Stage1Layout)
    (pCostSign pCostLens : ℕ) : List ℕ :=
  let C := I.compress
  let L := costScaleBits I
  let T_U := bitScalingPhases I
  let K_cap := T_U / k + 2
  [C.n, I.m, k, L, T_U, K_cap, lowerClip I.m, upperClip I.m, freezeThreshold I.m,
   narrowCostRounds C, lay.pCompTail, lay.pCompHead, pCostSign, pCostLens,
   lay.pAdjCostPtrs, lay.pCapBuf, lay.pFlow, lay.pResFwdBuf, lay.pTmp1, lay.pTmp2,
   lay.pFrozen, lay.pHSign, lay.pHMag, lay.pResIn]

/-- Persistent Stage 1 working-memory assertion across rounds `j = 0 .. narrowCostRounds C`,
holding all context pointers, fixed arrays, adjusted cost limbs, padded capacities, current flow
limbs `flowLimbs`, and small state `(s.frozen, s.halfCost)`. -/
def stage1WorkingAssn (I : Circulation) (k : ℕ) (lay : Stage1Layout)
    (pCostSign pCostLens : ℕ)
    (capLimbs : List (List ℕ)) (costLimbs : List (List ℕ))
    (adjPtrs : List ℕ) (adjLimbs : List (List ℕ))
    (s : NarrowCostState I.compress) (flowLimbs : Fin I.m → List ℕ)
    (resCSign resCMag resCapLens resOut : List ℕ)
    (resFwdLimbs : Fin I.m → List ℕ) (tmp1 tmp2 : List ℕ) : Assn :=
  let C := I.compress
  let K_cap := bitScalingPhases I / k + 2
  let tList := List.ofFn fun e : Fin I.m => (C.tail e).val
  let hList := List.ofFn fun e : Fin I.m => (C.head e).val
  let fwdPtrs := List.ofFn fun e : Fin I.m => lay.pResFwdBuf + e.val * K_cap
  let revPtrs := List.ofFn fun e : Fin I.m => lay.pFlow + e.val * K_cap
  Assn.list lay.pCtx (stage1CtxWords I k lay pCostSign pCostLens) *
  Assn.list lay.pResIn
    [C.n, 2 * I.m, k, lay.pResTail, lay.pResHead, lay.pResCSign, lay.pResCMag,
     lay.pResCapPtrs, lay.pResCapLens] *
  Assn.list lay.pResOut resOut *
  Assn.list lay.pCompTail tList *
  Assn.list lay.pCompHead hList *
  Assn.list lay.pAdjCostPtrs adjPtrs *
  (∏ j ∈ Finset.range I.m, Assn.list (adjPtrs.getD j 0) (adjLimbs.getD j [])) *
  Assn.list lay.pFrozen (List.ofFn fun e : Fin I.m => freezeCode (s.frozen e)) *
  Assn.list lay.pHSign (List.ofFn fun e : Fin I.m => if s.halfCost e < 0 then 1 else 0) *
  Assn.list lay.pHMag (List.ofFn fun e : Fin I.m => (s.halfCost e).natAbs) *
  Assn.list lay.pResTail (tList ++ hList) *
  Assn.list lay.pResHead (hList ++ tList) *
  Assn.list lay.pResCSign resCSign *
  Assn.list lay.pResCMag resCMag *
  Assn.list lay.pResCapPtrs (fwdPtrs ++ revPtrs) *
  Assn.list lay.pResCapLens resCapLens *
  (∏ j ∈ Finset.range I.m, Assn.list (lay.pCapBuf + j * K_cap) (padLimbs K_cap (capLimbs.getD j []))) *
  (∏ j ∈ Finset.range I.m, Assn.list (lay.pFlow + j * K_cap) (if h : j < I.m then flowLimbs ⟨j, h⟩ else [])) *
  (∏ j ∈ Finset.range I.m, Assn.list (lay.pResFwdBuf + j * K_cap) (if h : j < I.m then resFwdLimbs ⟨j, h⟩ else [])) *
  Assn.list lay.pTmp1 tmp1 *
  Assn.list lay.pTmp2 tmp2 *
  ⌜costLimbs.length = I.m ∧ adjPtrs.length = I.m ∧ adjLimbs.length = I.m ∧
    resCSign.length = 2 * I.m ∧ resCMag.length = 2 * I.m ∧ resCapLens.length = 2 * I.m ∧
    resOut.length = 4 ∧ tmp1.length = K_cap ∧ tmp2.length = K_cap ∧
    (∀ e : Fin I.m, (resFwdLimbs e).length = K_cap)⌝

end MinCostFlow.NarrowProg.Stage1
