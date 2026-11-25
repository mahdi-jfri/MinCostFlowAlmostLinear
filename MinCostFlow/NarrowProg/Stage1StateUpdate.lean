module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import WordRAM.Std.Array
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1StartHelpers
public import MinCostFlow.NarrowProg.Stage1CostBit
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Stage 1 round `(frozen, halfCost)` state update (`stage1StateUpdate`)

Implements the per-round `(frozen, halfCost)` state update of Stage 1:
- `stage1StepActive`: updates singleton cells `(pF + e, pS + e, pM + e)` for one active edge `e`
  using an overflow-free unsigned `(pos, neg)` split matching `stepHalfCost`.
- `stage1LoadAndStep`: loads `(u, v, dyu, dyv, hs, hm)` for active edge `e` and calls
  `stage1StepActive`.
- `stage1StateUpdate`: loops `e ∈ 0 .. m`, reads one cost bit per active edge via `stage1CostBit`,
  and updates `(pFrozen, pHSign, pHMag)` (`O(m + 1)`).
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Scaling.Machine
  MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate

private theorem list_eq_prod_singleton (p : ℕ) (xs : List ℕ) :
    Assn.list p xs = ∏ i ∈ Finset.range xs.length, Assn.list (p + i) [xs.getD i 0] := by
  have h : ∀ k ≤ xs.length, Assn.list p (xs.take k) =
      ∏ i ∈ Finset.range k, Assn.list (p + i) [xs.getD i 0] := by
    intro k
    induction k with
    | zero => intro _; simp [Assn.list]
    | succ k ih =>
      intro hk
      rw [Finset.prod_range_succ, ← ih (by omega),
        List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        Assn.list_append, List.length_take, Nat.min_eq_left (by omega),
        List.getD_eq_getElem _ _ (by omega)]
  simpa using h xs.length le_rfl

/-! ### 1. Single-edge active `(frozen, halfCost)` update (`stage1StepActive`) -/

/-- Update `(pFrozen[e], pHSign[e], pHMag[e])` for one active edge `e` using the unsigned
`(pos, neg)` split matching `stepHalfCost theta .none x bit (dyu - dyv)`. -/
wram_def stage1StepActive (hs, hm, bit, dyu, dyv, theta, pF, pS, pM, e) {
  pos := bit + 4 * dyv
  neg := 4 * dyu
  if hs == 0 {
    pos := pos + 2 * hm
  } else {
    neg := neg + 2 * hm
  }
  if pos < neg {
    d := neg - pos
    if d < theta {
      mem[pS + e] := 1
      mem[pM + e] := d
    } else {
      mem[pF + e] := 2
      mem[pS + e] := 0
      mem[pM + e] := 0
    }
  } else {
    d := pos - neg
    if d < theta {
      mem[pS + e] := 0
      mem[pM + e] := d
    } else {
      mem[pF + e] := 1
      mem[pS + e] := 0
      mem[pM + e] := 0
    }
  }
  return 0
}

structure Stage1StepActiveIn where
  x : ℤ
  bit : ℕ
  dyu : ℕ
  dyv : ℕ
  theta : ℕ
  e : ℕ
  oldS : ℕ
  oldM : ℕ

def stage1StepActiveSpec (w : ℕ) : Spec Stage1StepActiveIn where
  pre := fun g args => ⨆ (pF : ℕ) (pS : ℕ) (pM : ℕ),
    ⌜args = [if g.x < 0 then 1 else 0, g.x.natAbs, g.bit, g.dyu, g.dyv, g.theta, pF, pS, pM, g.e] ∧
      g.bit ≤ 1 ∧
      g.bit + 4 * g.dyv + 2 * g.x.natAbs < 2 ^ w ∧
      4 * g.dyu + 2 * g.x.natAbs < 2 ^ w ∧
      4 < 2 ^ w⌝ *
    Assn.list (pF + g.e) [0] * Assn.list (pS + g.e) [g.oldS] * Assn.list (pM + g.e) [g.oldM]
  post := fun g args v => ⨆ (pF : ℕ) (pS : ℕ) (pM : ℕ),
    let next := stepHalfCost g.theta .none g.x (g.bit : ℤ) ((g.dyu : ℤ) - (g.dyv : ℤ))
    ⌜args = [if g.x < 0 then 1 else 0, g.x.natAbs, g.bit, g.dyu, g.dyv, g.theta, pF, pS, pM, g.e] ∧
      v = 0⌝ *
    Assn.list (pF + g.e) [freezeCode next.1] *
    Assn.list (pS + g.e) [if next.2 < 0 then 1 else 0] *
    Assn.list (pM + g.e) [next.2.natAbs]

private theorem stepHalfCost_of_lt {theta pos neg : ℕ} {x : ℤ} {bit dyu dyv : ℕ}
    (hdiff : (pos : ℤ) - (neg : ℤ) = 2 * x + (bit : ℤ) - 4 * ((dyu : ℤ) - (dyv : ℤ)))
    (hlt : pos < neg) :
    let res := stepHalfCost theta .none x (bit : ℤ) ((dyu : ℤ) - (dyv : ℤ))
    (neg - pos < theta → freezeCode res.1 = 0 ∧ (if res.2 < 0 then 1 else 0) = 1 ∧ res.2.natAbs = neg - pos) ∧
    (theta ≤ neg - pos → freezeCode res.1 = 2 ∧ (if res.2 < 0 then 1 else 0) = 0 ∧ res.2.natAbs = 0) := by
  dsimp only [stepHalfCost]
  rw [← hdiff]
  constructor
  · intro hd
    have h1 : ¬ ((theta : ℤ) ≤ (pos : ℤ) - (neg : ℤ)) := by omega
    have h2 : ¬ ((pos : ℤ) - (neg : ℤ) ≤ -(theta : ℤ)) := by omega
    simp only [h1, h2, ↓reduceIte, freezeCode]
    refine ⟨trivial, ?_, by omega⟩
    split_ifs <;> omega
  · intro hd
    have h1 : ¬ ((theta : ℤ) ≤ (pos : ℤ) - (neg : ℤ)) := by omega
    have h2 : (pos : ℤ) - (neg : ℤ) ≤ -(theta : ℤ) := by omega
    simp only [h1, h2, ↓reduceIte, freezeCode, lt_self_iff_false, Int.natAbs_zero, and_self]

private theorem stepHalfCost_of_ge {theta pos neg : ℕ} {x : ℤ} {bit dyu dyv : ℕ}
    (hdiff : (pos : ℤ) - (neg : ℤ) = 2 * x + (bit : ℤ) - 4 * ((dyu : ℤ) - (dyv : ℤ)))
    (hge : neg ≤ pos) :
    let res := stepHalfCost theta .none x (bit : ℤ) ((dyu : ℤ) - (dyv : ℤ))
    (pos - neg < theta → freezeCode res.1 = 0 ∧ (if res.2 < 0 then 1 else 0) = 0 ∧ res.2.natAbs = pos - neg) ∧
    (theta ≤ pos - neg → freezeCode res.1 = 1 ∧ (if res.2 < 0 then 1 else 0) = 0 ∧ res.2.natAbs = 0) := by
  dsimp only [stepHalfCost]
  rw [← hdiff]
  constructor
  · intro hd
    have h1 : ¬ ((theta : ℤ) ≤ (pos : ℤ) - (neg : ℤ)) := by omega
    have h2 : ¬ ((pos : ℤ) - (neg : ℤ) ≤ -(theta : ℤ)) := by omega
    simp only [h1, h2, ↓reduceIte, freezeCode]
    refine ⟨trivial, ?_, by omega⟩
    split_ifs <;> omega
  · intro hd
    have h1 : (theta : ℤ) ≤ (pos : ℤ) - (neg : ℤ) := by omega
    simp only [h1, ↓reduceIte, freezeCode, lt_self_iff_false, Int.natAbs_zero, and_self]

theorem stage1StepActive_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1StepActive) :
    Meets w p f ((stage1StepActiveSpec w).withCost fun _ _ => 70) := by
  sep_enter g with hbit hpos_lt hneg_lt hw
  obtain ⟨x, bit, dyu, dyv, theta, e, oldS, oldM⟩ := g
  dsimp only at hbit hpos_lt hneg_lt hw ⊢
  by_cases hneg : x < 0
  · simp only [hneg, ↓reduceIte]
    have hdiff : ((bit + 4 * dyv : ℕ) : ℤ) - ((4 * dyu + 2 * x.natAbs : ℕ) : ℤ) =
        2 * x + (bit : ℤ) - 4 * ((dyu : ℤ) - (dyv : ℤ)) := by omega
    sep_step; sep_step; sep_step; sep_step; sep_step
    · have ⟨h1, h2⟩ := stepHalfCost_of_lt (theta := theta) hdiff (by omega)
      sep_step; sep_step; sep_step
      · obtain ⟨ha, hb, hc⟩ := h1 (by omega)
        sep_run
      · obtain ⟨ha, hb, hc⟩ := h2 (by omega)
        sep_run
    · have ⟨h1, h2⟩ := stepHalfCost_of_ge (theta := theta) hdiff (by omega)
      sep_step; sep_step; sep_step
      · obtain ⟨ha, hb, hc⟩ := h1 (by omega)
        sep_run
      · obtain ⟨ha, hb, hc⟩ := h2 (by omega)
        sep_run
  · simp only [hneg, ↓reduceIte]
    have hdiff : ((bit + 4 * dyv + 2 * x.natAbs : ℕ) : ℤ) - ((4 * dyu : ℕ) : ℤ) =
        2 * x + (bit : ℤ) - 4 * ((dyu : ℤ) - (dyv : ℤ)) := by omega
    sep_step; sep_step; sep_step; sep_step; sep_step
    · have ⟨h1, h2⟩ := stepHalfCost_of_lt (theta := theta) hdiff (by omega)
      sep_step; sep_step; sep_step
      · obtain ⟨ha, hb, hc⟩ := h1 (by omega)
        sep_run
      · obtain ⟨ha, hb, hc⟩ := h2 (by omega)
        sep_run
    · have ⟨h1, h2⟩ := stepHalfCost_of_ge (theta := theta) hdiff (by omega)
      sep_step; sep_step; sep_step
      · obtain ⟨ha, hb, hc⟩ := h1 (by omega)
        sep_run
      · obtain ⟨ha, hb, hc⟩ := h2 (by omega)
        sep_run

/-! ### 2. Load-and-step helper (`stage1LoadAndStep`) -/

/-- Read-only graph endpoints and dual potentials bundled as a single opaque atom across the
`stage1StateUpdate` loop. -/
def stateUpdRO (C : Circulation) (dy : Fin C.n → ℤ) (pCompTail pCompHead pDy : ℕ) : Assn :=
  Assn.list pCompTail (List.ofFn fun i : Fin C.m => (C.tail i).val) *
  Assn.list pCompHead (List.ofFn fun i : Fin C.m => (C.head i).val) *
  Assn.list pDy ((List.ofFn dy).flatMap encodeSignedPair)

/-- Load `(u, v, dyu, dyv, hs, hm)` for active edge `e` and call `stage1StepActive`. -/
wram_def stage1LoadAndStep (stepActIdx : ℕ)
    (bit, theta, pCompTail, pCompHead, pDy, pFrozen, pHSign, pHMag, e) {
  u := mem[pCompTail + e]
  v := mem[pCompHead + e]
  dyu := mem[pDy + 2 * u + 1]
  dyv := mem[pDy + 2 * v + 1]
  hs := mem[pHSign + e]
  hm := mem[pHMag + e]
  r := stepActIdx(hs, hm, bit, dyu, dyv, theta, pFrozen, pHSign, pHMag, e)
  return 0
}

structure Stage1LoadStepIn where
  C : Circulation
  bit : ℕ
  theta : ℕ
  e : Fin C.m
  x : ℤ
  dy : Fin C.n → ℤ

private theorem flatMap_encodeInt_len {n : ℕ} (dy : Fin n → ℤ) :
    ((List.ofFn dy).flatMap encodeSignedPair).length = 2 * n := by
  rw [List.length_flatMap]
  have hmap : ((List.ofFn dy).map (fun z => (encodeSignedPair z).length)) = List.replicate n 2 := by
    refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
    simp [encodeSignedPair]
  rw [hmap, List.sum_replicate, smul_eq_mul]; omega

private theorem flatMap_encodeInt_mag {n : ℕ} (dy : Fin n → ℤ) (v : Fin n) :
    ((List.ofFn dy).flatMap encodeSignedPair)[2 * v.val + 1]'(by rw [flatMap_encodeInt_len]; omega) =
      (dy v).natAbs := by
  have hat : ListAt (fun a => ((List.ofFn dy).flatMap encodeSignedPair).getD a 0) 0
      ((List.ofFn dy).flatMap encodeSignedPair) := fun i hi => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hp := integers_pair_at (List.ofFn dy) _ 0 hat ⟨v.val, by simp [v.isLt]⟩
  have h1 := hp 1 (by simp [encodeSignedPair])
  simp only [Nat.zero_add, encodeSignedPair, List.getElem_cons_succ, List.getElem_cons_zero] at h1
  have hl1 : 2 * v.val + 1 < ((List.ofFn dy).flatMap encodeSignedPair).length := by
    rw [flatMap_encodeInt_len]; omega
  have hl2 : v.val < (List.ofFn dy).length := by simp [v.isLt]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl1,
    List.getElem?_eq_getElem hl2, Option.getD_some, List.getElem_ofFn] at h1
  exact h1

def stage1LoadAndStepSpec (w : ℕ) : Spec Stage1LoadStepIn where
  pre := fun g args =>
    ⨆ (pCompTail : ℕ) (pCompHead : ℕ) (pDy : ℕ) (pFrozen : ℕ) (pHSign : ℕ) (pHMag : ℕ),
      ⌜args = [g.bit, g.theta, pCompTail, pCompHead, pDy, pFrozen, pHSign, pHMag, g.e.val] ∧
        g.bit ≤ 1 ∧ 4 < 2 ^ w ∧
        0 ≤ g.dy (g.C.tail g.e) ∧ 0 ≤ g.dy (g.C.head g.e) ∧
        g.bit + 4 * (g.dy (g.C.head g.e)).natAbs + 2 * g.x.natAbs < 2 ^ w ∧
        4 * (g.dy (g.C.tail g.e)).natAbs + 2 * g.x.natAbs < 2 ^ w⌝ *
      stateUpdRO g.C g.dy pCompTail pCompHead pDy *
      Assn.list (pFrozen + g.e.val) [0] *
      Assn.list (pHSign + g.e.val) [if g.x < 0 then 1 else 0] *
      Assn.list (pHMag + g.e.val) [g.x.natAbs]
  post := fun g args v =>
    ⨆ (pCompTail : ℕ) (pCompHead : ℕ) (pDy : ℕ) (pFrozen : ℕ) (pHSign : ℕ) (pHMag : ℕ),
      let res := stepHalfCost g.theta .none g.x (g.bit : ℤ)
        (g.dy (g.C.tail g.e) - g.dy (g.C.head g.e))
      ⌜args = [g.bit, g.theta, pCompTail, pCompHead, pDy, pFrozen, pHSign, pHMag, g.e.val] ∧ v = 0⌝ *
      stateUpdRO g.C g.dy pCompTail pCompHead pDy *
      Assn.list (pFrozen + g.e.val) [freezeCode res.1] *
      Assn.list (pHSign + g.e.val) [if res.2 < 0 then 1 else 0] *
      Assn.list (pHMag + g.e.val) [res.2.natAbs]

private theorem stateUpdRO_eq (C : Circulation) (dy : Fin C.n → ℤ) (pCompTail pCompHead pDy : ℕ) :
    stateUpdRO C dy pCompTail pCompHead pDy =
      Assn.list pCompTail (List.ofFn fun i : Fin C.m => (C.tail i).val) *
      Assn.list pCompHead (List.ofFn fun i : Fin C.m => (C.head i).val) *
      Assn.list pDy ((List.ofFn dy).flatMap encodeSignedPair) := rfl

theorem stage1LoadAndStep_meets {w : ℕ} {p : Program} {f stepActIdx : ℕ}
    (hp : p.procs[f]? = some (stage1LoadAndStep stepActIdx))
    (hsa : Meets w p stepActIdx ((stage1StepActiveSpec w).withCost fun _ _ => 70)) :
    Meets w p f ((stage1LoadAndStepSpec w).withCost fun _ _ => 130) := by
  sep_enter g with hbit hw hdyu0 hdyv0 hpos_lt hneg_lt
  obtain ⟨C, bit, theta, e, x, dy⟩ := g
  dsimp only at hbit hw hdyu0 hdyv0 hpos_lt hneg_lt ⊢
  sep_apply stateUpdRO_eq C dy pCompTail pCompHead pDy
  have hdy_len : ((List.ofFn dy).flatMap encodeSignedPair).length = 2 * C.n := flatMap_encodeInt_len dy
  have ht_e : (List.ofFn fun i : Fin C.m => (C.tail i).val)[e.val]'(by simp) =
      (C.tail e).val := List.getElem_ofFn ..
  have hh_e : (List.ofFn fun i : Fin C.m => (C.head i).val)[e.val]'(by simp) =
      (C.head e).val := List.getElem_ofFn ..
  have hdyu_mag := flatMap_encodeInt_mag dy (C.tail e)
  have hdyv_mag := flatMap_encodeInt_mag dy (C.head e)
  sep_step; rw [ht_e] at hu; subst hu
  sep_step; rw [hh_e] at hv; subst hv
  sep_step; rw [hdyu_mag] at hdyu; subst hdyu
  sep_step; rw [hdyv_mag] at hdyv; subst hdyv
  sep_step; sep_step
  sep_apply (stateUpdRO_eq C dy pCompTail pCompHead pDy).symm
  sep_step from ⟨x, bit, (dy (C.tail e)).natAbs, (dy (C.head e)).natAbs,
    theta, e.val, if x < 0 then 1 else 0, x.natAbs⟩
  have hdy_diff : ((dy (C.tail e)).natAbs : ℤ) - ((dy (C.head e)).natAbs : ℤ) =
      dy (C.tail e) - dy (C.head e) := by omega
  rw [hdy_diff]
  sep_run

/-! ### 3. All-edges `(frozen, halfCost)` update (`stage1StateUpdate`) -/

/-- Update `(pFrozen, pHSign, pHMag)` across all `m` edges using one cost bit per active edge
and the nonnegative dual potential table `pDy`. -/
wram_def stage1StateUpdate (costBitIdx loadStepIdx : ℕ)
    (m, k, L, j, theta, pCompTail, pCompHead, pCostSign, pAdjPtrs, pCostLens,
      pFrozen, pHSign, pHMag, pDy) {
  for e in 0 .. m {
    fr := mem[pFrozen + e]
    if fr == 0 {
      fr := mem[pCostSign + e]
      cPtr := mem[pAdjPtrs + e]
      cLen := mem[pCostLens + e]
      bit := costBitIdx(fr, cPtr, cLen, L, j, k)
      fr := loadStepIdx(bit, theta, pCompTail, pCompHead, pDy, pFrozen, pHSign, pHMag, e)
    }
    fr := 0
  }
  return 0
}

structure Stage1StateUpdIn where
  C : Circulation
  k : ℕ
  L : ℕ
  j : ℕ
  theta : ℕ
  fr : Fin C.m → FreezeState
  x : Fin C.m → ℤ
  dy : Fin C.n → ℤ
  adjPtrs : List ℕ
  adjLimbs : List (List ℕ)

def nextFrList (C : Circulation) (L j theta : ℕ)
    (fr : Fin C.m → FreezeState) (x : Fin C.m → ℤ) (dy : Fin C.n → ℤ) : List ℕ :=
  List.ofFn fun e : Fin C.m => freezeCode (stepHalfCost theta (fr e) (x e)
    (costBit (C.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ))) (dy (C.tail e) - dy (C.head e))).1

def nextHSList (C : Circulation) (L j theta : ℕ)
    (fr : Fin C.m → FreezeState) (x : Fin C.m → ℤ) (dy : Fin C.n → ℤ) : List ℕ :=
  List.ofFn fun e : Fin C.m =>
    if (stepHalfCost theta (fr e) (x e)
      (costBit (C.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ))) (dy (C.tail e) - dy (C.head e))).2 < 0
    then 1 else 0

def nextHMList (C : Circulation) (L j theta : ℕ)
    (fr : Fin C.m → FreezeState) (x : Fin C.m → ℤ) (dy : Fin C.n → ℤ) : List ℕ :=
  List.ofFn fun e : Fin C.m =>
    (stepHalfCost theta (fr e) (x e)
      (costBit (C.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ))) (dy (C.tail e) - dy (C.head e))).2.natAbs

def stage1StateUpdateSpec (w : ℕ) : Spec Stage1StateUpdIn where
  pre := fun g args =>
    ⨆ (pCompTail : ℕ) (pCompHead : ℕ) (pCostSign : ℕ) (pAdjPtrs : ℕ) (pCostLens : ℕ)
      (pFrozen : ℕ) (pHSign : ℕ) (pHMag : ℕ) (pDy : ℕ),
      ⌜args = [g.C.m, g.k, g.L, g.j, g.theta, pCompTail, pCompHead, pCostSign, pAdjPtrs,
          pCostLens, pFrozen, pHSign, pHMag, pDy] ∧
        g.adjPtrs.length = g.C.m ∧ g.adjLimbs.length = g.C.m ∧
        1 ≤ g.k ∧ 4 < 2 ^ w ∧
        (∀ e : Fin g.C.m, Limbs g.k (g.adjLimbs.getD e.val []) ∧
          Nat.ofDigits (2 ^ g.k) (g.adjLimbs.getD e.val []) =
            if g.C.cost e < 0 then (g.C.cost e).natAbs - 1 else (g.C.cost e).natAbs) ∧
        (∀ v : Fin g.C.n, 0 ≤ g.dy v) ∧
        (∀ e : Fin g.C.m,
          1 + 4 * (g.dy (g.C.head e)).natAbs + 2 * (g.x e).natAbs < 2 ^ w ∧
          4 * (g.dy (g.C.tail e)).natAbs + 2 * (g.x e).natAbs < 2 ^ w) ∧
        (∀ e : Fin g.C.m, g.fr e ≠ .none → g.x e = 0)⌝ *
      Assn.list pCompTail (List.ofFn fun e : Fin g.C.m => (g.C.tail e).val) *
      Assn.list pCompHead (List.ofFn fun e : Fin g.C.m => (g.C.head e).val) *
      Assn.list pCostSign (List.ofFn fun e : Fin g.C.m => if g.C.cost e < 0 then 1 else 0) *
      Assn.list pAdjPtrs g.adjPtrs *
      Assn.list pCostLens (g.adjLimbs.map List.length) *
      (∏ e ∈ Finset.range g.C.m, Assn.list (g.adjPtrs.getD e 0) (g.adjLimbs.getD e [])) *
      Assn.list pFrozen (List.ofFn fun e : Fin g.C.m => freezeCode (g.fr e)) *
      Assn.list pHSign (List.ofFn fun e : Fin g.C.m => if g.x e < 0 then 1 else 0) *
      Assn.list pHMag (List.ofFn fun e : Fin g.C.m => (g.x e).natAbs) *
      Assn.list pDy ((List.ofFn g.dy).flatMap encodeSignedPair)
  post := fun g args v =>
    ⨆ (pCompTail : ℕ) (pCompHead : ℕ) (pCostSign : ℕ) (pAdjPtrs : ℕ) (pCostLens : ℕ)
      (pFrozen : ℕ) (pHSign : ℕ) (pHMag : ℕ) (pDy : ℕ),
      ⌜args = [g.C.m, g.k, g.L, g.j, g.theta, pCompTail, pCompHead, pCostSign, pAdjPtrs,
          pCostLens, pFrozen, pHSign, pHMag, pDy] ∧ v = 0⌝ *
      Assn.list pCompTail (List.ofFn fun e : Fin g.C.m => (g.C.tail e).val) *
      Assn.list pCompHead (List.ofFn fun e : Fin g.C.m => (g.C.head e).val) *
      Assn.list pCostSign (List.ofFn fun e : Fin g.C.m => if g.C.cost e < 0 then 1 else 0) *
      Assn.list pAdjPtrs g.adjPtrs *
      Assn.list pCostLens (g.adjLimbs.map List.length) *
      (∏ e ∈ Finset.range g.C.m, Assn.list (g.adjPtrs.getD e 0) (g.adjLimbs.getD e [])) *
      Assn.list pFrozen (nextFrList g.C g.L g.j g.theta g.fr g.x g.dy) *
      Assn.list pHSign (nextHSList g.C g.L g.j g.theta g.fr g.x g.dy) *
      Assn.list pHMag (nextHMList g.C g.L g.j g.theta g.fr g.x g.dy) *
      Assn.list pDy ((List.ofFn g.dy).flatMap encodeSignedPair)

private def stateUpdCostCell (pCostSign pAdjPtrs pCostLens : ℕ)
    (csL adjPtrs : List ℕ) (adjLimbs : List (List ℕ)) (i : ℕ) : Assn :=
  Assn.list (pCostSign + i) [csL.getD i 0] *
  Assn.list (pAdjPtrs + i) [adjPtrs.getD i 0] *
  Assn.list (pCostLens + i) [(adjLimbs.getD i []).length] *
  Assn.list (adjPtrs.getD i 0) (adjLimbs.getD i [])

private def stateUpdEdgeCell (pFrozen pHSign pHMag : ℕ)
    (newF newS newM oldF oldS oldM : List ℕ) (e i : ℕ) : Assn :=
  Assn.list (pFrozen + i) [if i < e then newF.getD i 0 else oldF.getD i 0] *
  Assn.list (pHSign + i) [if i < e then newS.getD i 0 else oldS.getD i 0] *
  Assn.list (pHMag + i) [if i < e then newM.getD i 0 else oldM.getD i 0]

private theorem stateUpdCostCell_eq {m pCostSign pAdjPtrs pCostLens : ℕ}
    {csL adjPtrs : List ℕ} {adjLimbs : List (List ℕ)}
    (hcs : csL.length = m) (hap : adjPtrs.length = m) (hal : adjLimbs.length = m) :
    Assn.list pCostSign csL * Assn.list pAdjPtrs adjPtrs *
    Assn.list pCostLens (adjLimbs.map List.length) *
    (∏ i ∈ Finset.range m, Assn.list (adjPtrs.getD i 0) (adjLimbs.getD i [])) =
      ∏ i ∈ Finset.range m, stateUpdCostCell pCostSign pAdjPtrs pCostLens csL adjPtrs adjLimbs i := by
  rw [list_eq_prod_singleton pCostSign csL, list_eq_prod_singleton pAdjPtrs adjPtrs,
    list_eq_prod_singleton pCostLens (adjLimbs.map List.length),
    hcs, hap, List.length_map, hal]
  have hlen_congr :
      (∏ i ∈ Finset.range m, Assn.list (pCostLens + i) [(adjLimbs.map List.length).getD i 0]) =
      ∏ i ∈ Finset.range m, Assn.list (pCostLens + i) [(adjLimbs.getD i []).length] :=
    Finset.prod_congr rfl fun i hi => by
      have him : i < m := Finset.mem_range.mp hi
      rw [List.getD_eq_getElem _ _ (by simp [hal, him]), List.getElem_map,
        List.getD_eq_getElem _ _ (by omega : i < adjLimbs.length)]
  rw [hlen_congr]
  simp only [stateUpdCostCell, Finset.prod_mul_distrib, mul_assoc]

private theorem stateUpdEdgeCell_init {m pFrozen pHSign pHMag : ℕ}
    {newF newS newM oldF oldS oldM : List ℕ}
    (hf : oldF.length = m) (hs : oldS.length = m) (hm : oldM.length = m) :
    Assn.list pFrozen oldF * Assn.list pHSign oldS * Assn.list pHMag oldM =
      ∏ i ∈ Finset.range m, stateUpdEdgeCell pFrozen pHSign pHMag newF newS newM oldF oldS oldM 0 i := by
  rw [list_eq_prod_singleton pFrozen oldF, list_eq_prod_singleton pHSign oldS,
    list_eq_prod_singleton pHMag oldM, hf, hs, hm]
  simp only [stateUpdEdgeCell, Nat.not_lt_zero, ↓reduceIte, Finset.prod_mul_distrib, mul_assoc]

private theorem stateUpdEdgeCell_final {m pFrozen pHSign pHMag : ℕ}
    {newF newS newM oldF oldS oldM : List ℕ}
    (hf : newF.length = m) (hs : newS.length = m) (hm : newM.length = m) :
    (∏ i ∈ Finset.range m, stateUpdEdgeCell pFrozen pHSign pHMag newF newS newM oldF oldS oldM m i) =
      Assn.list pFrozen newF * Assn.list pHSign newS * Assn.list pHMag newM := by
  have hcongr :
      (∏ i ∈ Finset.range m, stateUpdEdgeCell pFrozen pHSign pHMag newF newS newM oldF oldS oldM m i) =
      ∏ i ∈ Finset.range m,
        (Assn.list (pFrozen + i) [newF.getD i 0] *
         Assn.list (pHSign + i) [newS.getD i 0] *
         Assn.list (pHMag + i) [newM.getD i 0]) :=
    Finset.prod_congr rfl fun i hi => by
      simp only [stateUpdEdgeCell, Finset.mem_range.mp hi, ↓reduceIte]
  rw [hcongr]
  simp only [Finset.prod_mul_distrib]
  rw [list_eq_prod_singleton pFrozen newF, list_eq_prod_singleton pHSign newS,
    list_eq_prod_singleton pHMag newM, hf, hs, hm]

private theorem stateUpdEdgeCell_step {m pFrozen pHSign pHMag : ℕ}
    {newF newS newM oldF oldS oldM : List ℕ} {e : ℕ} (he : e < m) :
    Assn.list (pFrozen + e) [newF.getD e 0] *
    Assn.list (pHSign + e) [newS.getD e 0] *
    Assn.list (pHMag + e) [newM.getD e 0] *
    (∏ i ∈ (Finset.range m).erase e,
      stateUpdEdgeCell pFrozen pHSign pHMag newF newS newM oldF oldS oldM e i) =
      ∏ i ∈ Finset.range m,
        stateUpdEdgeCell pFrozen pHSign pHMag newF newS newM oldF oldS oldM (e + 1) i := by
  have hmem : e ∈ Finset.range m := Finset.mem_range.mpr he
  rw [Assn.prod_eq_mul_erase hmem
    (stateUpdEdgeCell pFrozen pHSign pHMag newF newS newM oldF oldS oldM (e + 1))]
  congr 1
  · simp [stateUpdEdgeCell]
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ e := (Finset.mem_erase.mp hi).1
    have hiff : (i < e) ↔ (i < e + 1) := by omega
    simp only [stateUpdEdgeCell, hiff]

theorem stage1StateUpdate_meets {w : ℕ} {p : Program} {f costBitIdx loadStepIdx : ℕ} {Tcb : ℕ}
    (hp : p.procs[f]? = some (stage1StateUpdate costBitIdx loadStepIdx))
    (hcb : Meets w p costBitIdx ((stage1CostBitSpec w).withCost fun _ _ => Tcb))
    (hls : Meets w p loadStepIdx ((stage1LoadAndStepSpec w).withCost fun _ _ => 130)) :
    Meets w p f ((stage1StateUpdateSpec w).withCost fun g _ => (Tcb + 210) * g.C.m + 30) := by
  sep_enter g with hap hal hk hw hadj hdy0 hfit hfr0
  obtain ⟨C, k, L, j, theta, fr, x, dy, adjPtrs, adjLimbs⟩ := g
  dsimp only at hap hal hk hw hadj hdy0 hfit hfr0 ⊢
  have hcsL_len : (List.ofFn fun e : Fin C.m => if C.cost e < 0 then 1 else 0).length = C.m := List.length_ofFn
  have hcsL_get : ∀ e (he : e < C.m), (List.ofFn fun i : Fin C.m => if C.cost i < 0 then 1 else 0).getD e 0 =
      (if C.cost ⟨e, he⟩ < 0 then 1 else 0) := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  have holdF_len : (List.ofFn fun e : Fin C.m => freezeCode (fr e)).length = C.m := List.length_ofFn
  have holdS_len : (List.ofFn fun e : Fin C.m => if x e < 0 then 1 else 0).length = C.m := List.length_ofFn
  have holdM_len : (List.ofFn fun e : Fin C.m => (x e).natAbs).length = C.m := List.length_ofFn
  have hnewF_len : (nextFrList C L j theta fr x dy).length = C.m := List.length_ofFn
  have hnewS_len : (nextHSList C L j theta fr x dy).length = C.m := List.length_ofFn
  have hnewM_len : (nextHMList C L j theta fr x dy).length = C.m := List.length_ofFn
  have holdF_get : ∀ e (he : e < C.m), (List.ofFn fun i : Fin C.m => freezeCode (fr i)).getD e 0 =
      freezeCode (fr ⟨e, he⟩) := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  have holdS_get : ∀ e (he : e < C.m), (List.ofFn fun i : Fin C.m => if x i < 0 then 1 else 0).getD e 0 =
      (if x ⟨e, he⟩ < 0 then 1 else 0) := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  have holdM_get : ∀ e (he : e < C.m), (List.ofFn fun i : Fin C.m => (x i).natAbs).getD e 0 =
      (x ⟨e, he⟩).natAbs := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  have hnewF_get : ∀ e (he : e < C.m), (nextFrList C L j theta fr x dy).getD e 0 =
      freezeCode (stepHalfCost theta (fr ⟨e, he⟩) (x ⟨e, he⟩)
        (costBit (C.cost ⟨e, he⟩) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)))
        (dy (C.tail ⟨e, he⟩) - dy (C.head ⟨e, he⟩))).1 := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp [nextFrList]; omega)]; exact List.getElem_ofFn ..
  have hnewS_get : ∀ e (he : e < C.m), (nextHSList C L j theta fr x dy).getD e 0 =
      (if (stepHalfCost theta (fr ⟨e, he⟩) (x ⟨e, he⟩)
        (costBit (C.cost ⟨e, he⟩) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)))
        (dy (C.tail ⟨e, he⟩) - dy (C.head ⟨e, he⟩))).2 < 0 then 1 else 0) := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp [nextHSList]; omega)]; exact List.getElem_ofFn ..
  have hnewM_get : ∀ e (he : e < C.m), (nextHMList C L j theta fr x dy).getD e 0 =
      (stepHalfCost theta (fr ⟨e, he⟩) (x ⟨e, he⟩)
        (costBit (C.cost ⟨e, he⟩) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)))
        (dy (C.tail ⟨e, he⟩) - dy (C.head ⟨e, he⟩))).2.natAbs := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp [nextHMList]; omega)]; exact List.getElem_ofFn ..
  generalize hcsL_eq : (List.ofFn fun e : Fin C.m => if C.cost e < 0 then 1 else 0) = csL at hcsL_len hcsL_get ⊢
  generalize holdF_eq : (List.ofFn fun e : Fin C.m => freezeCode (fr e)) = oldF at holdF_len holdF_get ⊢
  generalize holdS_eq : (List.ofFn fun e : Fin C.m => if x e < 0 then 1 else 0) = oldS at holdS_len holdS_get ⊢
  generalize holdM_eq : (List.ofFn fun e : Fin C.m => (x e).natAbs) = oldM at holdM_len holdM_get ⊢
  generalize hnewF_eq : nextFrList C L j theta fr x dy = newF at hnewF_len hnewF_get ⊢
  generalize hnewS_eq : nextHSList C L j theta fr x dy = newS at hnewS_len hnewS_get ⊢
  generalize hnewM_eq : nextHMList C L j theta fr x dy = newM at hnewM_len hnewM_get ⊢
  sep_apply (stateUpdRO_eq C dy pCompTail pCompHead pDy).symm
  sep_apply stateUpdCostCell_eq hcsL_len hap hal
  sep_apply stateUpdEdgeCell_init (newF := newF) (newS := newS) (newM := newM)
    holdF_len holdS_len holdM_len
  sep_for (fun e (t : ℕ × ℕ × ℕ × ℕ) =>
    ⟨[C.m, k, L, j, theta, pCompTail, pCompHead, pCostSign, pAdjPtrs, pCostLens,
      pFrozen, pHSign, pHMag, pDy, e, t.1, t.2.1, t.2.2.1, t.2.2.2],
      e ≤ C.m, (Tcb + 195) * (C.m - e) + 5,
      [stateUpdRO C dy pCompTail pCompHead pDy,
       ∏ i ∈ Finset.range C.m, stateUpdCostCell pCostSign pAdjPtrs pCostLens csL adjPtrs adjLimbs i,
       ∏ i ∈ Finset.range C.m,
         stateUpdEdgeCell pFrozen pHSign pHMag newF newS newM oldF oldS oldM e i]⟩)
    with ⟨t0, t1, t2, t3⟩
  · have hmem : e ∈ Finset.range C.m := Finset.mem_range.mpr hhi
    have hmul_sub_z : ((Tcb : ℤ) + 195) * ((C.m : ℤ) - (e : ℤ)) =
        ((Tcb : ℤ) + 195) + ((Tcb : ℤ) + 195) * ((C.m : ℤ) - ((e + 1 : ℕ) : ℤ)) := by
      push_cast; ring
    sep_apply Assn.prod_eq_mul_erase hmem
      (stateUpdEdgeCell pFrozen pHSign pHMag newF newS newM oldF oldS oldM e)
    have hpopE : stateUpdEdgeCell pFrozen pHSign pHMag newF newS newM oldF oldS oldM e e =
        Assn.list (pFrozen + e) [oldF.getD e 0] *
        Assn.list (pHSign + e) [oldS.getD e 0] *
        Assn.list (pHMag + e) [oldM.getD e 0] := by
      simp [stateUpdEdgeCell]
    sep_apply hpopE
    rw [holdF_get e hhi, holdS_get e hhi, holdM_get e hhi]
    cases hfe : fr ⟨e, hhi⟩ with
    | none =>
      dsimp only [freezeCode]
      have hadj_e := hadj ⟨e, hhi⟩
      have hadj1 : Limbs k (adjLimbs.getD e []) := hadj_e.1
      have hadj2 : Nat.ofDigits (2 ^ k) (adjLimbs.getD e []) =
          if C.cost ⟨e, hhi⟩ < 0 then (C.cost ⟨e, hhi⟩).natAbs - 1 else (C.cost ⟨e, hhi⟩).natAbs :=
        hadj_e.2
      have hfit_e := hfit ⟨e, hhi⟩
      have hdyu_nonneg := hdy0 (C.tail ⟨e, hhi⟩)
      have hdyv_nonneg := hdy0 (C.head ⟨e, hhi⟩)
      sep_step
      sep_step
      sep_apply Assn.prod_eq_mul_erase hmem
        (stateUpdCostCell pCostSign pAdjPtrs pCostLens csL adjPtrs adjLimbs)
      have hpopC : stateUpdCostCell pCostSign pAdjPtrs pCostLens csL adjPtrs adjLimbs e =
          Assn.list (pCostSign + e) [csL.getD e 0] *
          Assn.list (pAdjPtrs + e) [adjPtrs.getD e 0] *
          Assn.list (pCostLens + e) [(adjLimbs.getD e []).length] *
          Assn.list (adjPtrs.getD e 0) (adjLimbs.getD e []) := rfl
      sep_apply hpopC
      rw [hcsL_get e hhi]
      sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
      subst hcPtr hcLen
      sep_step
      sep_step from (C.cost ⟨e, hhi⟩, k, adjLimbs.getD e [], L, j)
      have hbit_eq : (bit : ℤ) = costBit (C.cost ⟨e, hhi⟩) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) := by
        assumption
      rw [← hcsL_get e hhi]
      sep_apply hpopC.symm
      sep_apply (Assn.prod_eq_mul_erase hmem
        (stateUpdCostCell pCostSign pAdjPtrs pCostLens csL adjPtrs adjLimbs)).symm
      sep_step from ⟨C, bit, theta, ⟨e, hhi⟩, x ⟨e, hhi⟩, dy⟩
      have hcells :
          Assn.list (pFrozen + e)
            [freezeCode (stepHalfCost theta .none (x ⟨e, hhi⟩) (bit : ℤ)
              (dy (C.tail ⟨e, hhi⟩) - dy (C.head ⟨e, hhi⟩))).1] *
          Assn.list (pHSign + e)
            [if (stepHalfCost theta .none (x ⟨e, hhi⟩) (bit : ℤ)
              (dy (C.tail ⟨e, hhi⟩) - dy (C.head ⟨e, hhi⟩))).2 < 0 then 1 else 0] *
          Assn.list (pHMag + e)
            [(stepHalfCost theta .none (x ⟨e, hhi⟩) (bit : ℤ)
              (dy (C.tail ⟨e, hhi⟩) - dy (C.head ⟨e, hhi⟩))).2.natAbs] =
          Assn.list (pFrozen + e) [newF.getD e 0] *
          Assn.list (pHSign + e) [newS.getD e 0] *
          Assn.list (pHMag + e) [newM.getD e 0] := by
        rw [hnewF_get e hhi, hnewS_get e hhi, hnewM_get e hhi, hfe, hbit_eq]
      sep_apply hcells
      sep_apply stateUpdEdgeCell_step (pFrozen := pFrozen) (pHSign := pHSign) (pHMag := pHMag)
        (newF := newF) (newS := newS) (newM := newM)
        (oldF := oldF) (oldS := oldS) (oldM := oldM) hhi
      sep_run
    | pos =>
      dsimp only [freezeCode]
      have hx0 : x ⟨e, hhi⟩ = 0 := hfr0 ⟨e, hhi⟩ (by simp [hfe])
      have hnf : newF.getD e 0 = 1 := by rw [hnewF_get e hhi, hfe]; rfl
      have hns : newS.getD e 0 = 0 := by rw [hnewS_get e hhi, hfe]; simp [stepHalfCost]
      have hnm : newM.getD e 0 = 0 := by rw [hnewM_get e hhi, hfe]; simp [stepHalfCost]
      have hxs : (if x ⟨e, hhi⟩ < 0 then 1 else 0) = 0 := by simp [hx0]
      have hxm : (x ⟨e, hhi⟩).natAbs = 0 := by simp [hx0]
      rw [hxs, hxm]
      sep_step
      sep_step
      sep_step
      have hcells :
          Assn.list (pFrozen + e) [1] * Assn.list (pHSign + e) [0] * Assn.list (pHMag + e) [0] =
          Assn.list (pFrozen + e) [newF.getD e 0] * Assn.list (pHSign + e) [newS.getD e 0] *
            Assn.list (pHMag + e) [newM.getD e 0] := by
        rw [hnf, hns, hnm]
      sep_apply hcells
      sep_apply stateUpdEdgeCell_step (pFrozen := pFrozen) (pHSign := pHSign) (pHMag := pHMag)
        (newF := newF) (newS := newS) (newM := newM)
        (oldF := oldF) (oldS := oldS) (oldM := oldM) hhi
      sep_run
    | neg =>
      dsimp only [freezeCode]
      have hx0 : x ⟨e, hhi⟩ = 0 := hfr0 ⟨e, hhi⟩ (by simp [hfe])
      have hnf : newF.getD e 0 = 2 := by rw [hnewF_get e hhi, hfe]; rfl
      have hns : newS.getD e 0 = 0 := by rw [hnewS_get e hhi, hfe]; simp [stepHalfCost]
      have hnm : newM.getD e 0 = 0 := by rw [hnewM_get e hhi, hfe]; simp [stepHalfCost]
      have hxs : (if x ⟨e, hhi⟩ < 0 then 1 else 0) = 0 := by simp [hx0]
      have hxm : (x ⟨e, hhi⟩).natAbs = 0 := by simp [hx0]
      rw [hxs, hxm]
      sep_step
      sep_step
      sep_step
      have hcells :
          Assn.list (pFrozen + e) [2] * Assn.list (pHSign + e) [0] * Assn.list (pHMag + e) [0] =
          Assn.list (pFrozen + e) [newF.getD e 0] * Assn.list (pHSign + e) [newS.getD e 0] *
            Assn.list (pHMag + e) [newM.getD e 0] := by
        rw [hnf, hns, hnm]
      sep_apply hcells
      sep_apply stateUpdEdgeCell_step (pFrozen := pFrozen) (pHSign := pHSign) (pHMag := pHMag)
        (newF := newF) (newS := newS) (newM := newM)
        (oldF := oldF) (oldS := oldS) (oldM := oldM) hhi
      sep_run
  · sep_apply stateUpdRO_eq C dy pCompTail pCompHead pDy
    sep_apply (stateUpdCostCell_eq hcsL_len hap hal).symm
    sep_apply stateUpdEdgeCell_final (pFrozen := pFrozen) (pHSign := pHSign) (pHMag := pHMag)
      (oldF := oldF) (oldS := oldS) (oldM := oldM) hnewF_len hnewS_len hnewM_len
    rw [← hcsL_eq, ← hnewF_eq, ← hnewS_eq, ← hnewM_eq]
    sep_run

theorem stage1StateUpdate_meetsO {w : ℕ} {p : Program} {f costBitIdx loadStepIdx : ℕ}
    (hp : p.procs[f]? = some (stage1StateUpdate costBitIdx loadStepIdx))
    (hcb : MeetsO w p costBitIdx (stage1CostBitSpec w) fun _ _ => 1)
    (hls : Meets w p loadStepIdx ((stage1LoadAndStepSpec w).withCost fun _ _ => 130)) :
    MeetsO w p f (stage1StateUpdateSpec w) fun g _ => g.C.m + 1 :=
  MeetsO.of_callee hcb fun K hK =>
    ⟨_, stage1StateUpdate_meets hp hK hls, K + 210, fun g => by
      dsimp only; simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega⟩

/-- Polymorphic module for `stage1StateUpdate` and its helpers (parameterized by `limbBitName`). -/
def stage1StateUpdateMod {ι : Type}
    (name costBitName limbBitName loadStepName stepActName : ι) : Module ι :=
  ⟨[(costBitName, fun idx => stage1CostBit (idx limbBitName)),
    (stepActName, fun _ => stage1StepActive),
    (loadStepName, fun idx => stage1LoadAndStep (idx stepActName)),
    (name, fun idx => stage1StateUpdate (idx costBitName) (idx loadStepName))]⟩

theorem stage1StateUpdateMod_noRand {ι : Type}
    (name costBitName limbBitName loadStepName stepActName : ι) :
    (stage1StateUpdateMod name costBitName limbBitName loadStepName stepActName).NoRand := by
  wram_no_rand

theorem stage1StateUpdateMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {name costBitName limbBitName loadStepName stepActName : ι}
    (hp : (stage1StateUpdateMod name costBitName limbBitName loadStepName stepActName).Placed p idx)
    (hlb : MeetsO w p (idx limbBitName) (limbBitSpec w) fun _ _ => 1) :
    MeetsO w p (idx name) (stage1StateUpdateSpec w) fun g _ => g.C.m + 1 :=
  stage1StateUpdate_meetsO
    (hp.get (n := name) (b := fun i => stage1StateUpdate (i costBitName) (i loadStepName))
      (by simp [stage1StateUpdateMod]))
    (stage1CostBit_meetsO
      (hp.get (n := costBitName) (b := fun i => stage1CostBit (i limbBitName))
        (by simp [stage1StateUpdateMod])) hlb)
    (stage1LoadAndStep_meets
      (hp.get (n := loadStepName) (b := fun i => stage1LoadAndStep (i stepActName))
        (by simp [stage1StateUpdateMod]))
      (stage1StepActive_meets (hp.get (n := stepActName) (b := fun _ => stage1StepActive)
        (by simp [stage1StateUpdateMod]))))

end MinCostFlow.NarrowProg.Stage1
