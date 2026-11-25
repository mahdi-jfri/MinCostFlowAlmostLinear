module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Array
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.CostBits
public import MinCostFlow.NarrowProg.Stage1Defs
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Rounded costs of one Stage 1 round (`stage1RoundedCosts`)

Implements `narrowRoundedCosts` for one Stage 1 cost-scaling round:
- `stage1Min (a, b)`: branchless-style helper returning `min a b` (`O(1)`).
- `stage1RoundEdge`: writes the forward/reverse rounded cost pair `(fSign, fMag, rSign, rMag)` of a
  single edge `e` into singleton cells `(pFS + e, pRS + e, pFM + e, pRM + e)`, implementing
  `roundFwd` and `roundRev` (`O(1)`).
- `stage1RoundedCosts`: loops `e ∈ 0 .. m`, filling the `2 * m`-element residual cost sign and
  magnitude arrays `(pResCSign, pResCMag)` matching `narrowRoundedCosts C fr x` (`O(m + 1)`).
- `stage1RoundedCostsMod`: polymorphic `Module ι` (`NoRand`) bundling the three procedures.
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

/-! ### 0. Minimum helper (`stage1Min`) -/

/-- Return `min a b`. -/
wram_def stage1Min (a, b) {
  if a < b {
    return a
  } else {
    return b
  }
}

def stage1MinSpec (w : ℕ) : Spec (ℕ × ℕ) where
  pre := fun (a, b) args => ⌜args = [a, b] ∧ a < 2 ^ w ∧ b < 2 ^ w ∧ 1 < 2 ^ w⌝
  post := fun (a, b) args v => ⌜args = [a, b] ∧ v = min a b⌝

theorem stage1Min_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1Min) :
    Meets w p f ((stage1MinSpec w).withCost fun _ _ => 15) := by
  sep_enter ⟨a, b⟩ with ha hb hw
  sep_step
  · sep_run
  · sep_run

/-! ### 1. Single-edge rounding (`stage1RoundEdge`) -/

/-- Parameterized forward rounded cost matching `roundedForwardCost m` when `lo = lowerClip m`
and `up = upperClip m`. -/
def roundFwd (lo up : ℕ) (fr : FreezeState) (x : ℤ) : ℤ :=
  match fr with
  | .none => clampInt (-(lo : ℤ)) (up : ℤ) ((x + 1) / 2)
  | .pos => (up : ℤ)
  | .neg => -(lo : ℤ)

/-- Parameterized reverse rounded cost matching `roundedReverseCost m` when `lo = lowerClip m`
and `up = upperClip m`. -/
def roundRev (lo up : ℕ) (fr : FreezeState) (x : ℤ) : ℤ :=
  match fr with
  | .none => clampInt (-(lo : ℤ)) (up : ℤ) (-((x + 1) / 2))
  | .pos => -(lo : ℤ)
  | .neg => (up : ℤ)

private theorem roundFwd_nonneg {lo up : ℕ} (hlo : 0 < lo) {x : ℤ} (hx : 0 ≤ x) :
    (if roundFwd lo up .none x < 0 then 1 else 0) = 0 ∧
      (roundFwd lo up .none x).natAbs = min ((x.natAbs + 1) / 2) up := by
  unfold roundFwd clampInt
  have hdiv : (x + 1) / 2 = (((x.natAbs + 1) / 2 : ℕ) : ℤ) := by omega
  rw [hdiv]; simp only [max_def, min_def]; split_ifs <;> omega

private theorem roundRev_nonneg {lo up : ℕ} (hup : 0 < up) {x : ℤ} (hx : 0 ≤ x) :
    (if roundRev lo up .none x < 0 then 1 else 0) = min (min ((x.natAbs + 1) / 2) lo) 1 ∧
      (roundRev lo up .none x).natAbs = min ((x.natAbs + 1) / 2) lo := by
  unfold roundRev clampInt
  have hdiv : (x + 1) / 2 = (((x.natAbs + 1) / 2 : ℕ) : ℤ) := by omega
  rw [hdiv]; simp only [max_def, min_def]; split_ifs <;> omega

private theorem roundFwd_neg {lo up : ℕ} (hup : 0 < up) {x : ℤ} (hx : x < 0) :
    (if roundFwd lo up .none x < 0 then 1 else 0) = min (min (x.natAbs / 2) lo) 1 ∧
      (roundFwd lo up .none x).natAbs = min (x.natAbs / 2) lo := by
  unfold roundFwd clampInt
  have hdiv : (x + 1) / 2 = -((x.natAbs / 2 : ℕ) : ℤ) := by omega
  rw [hdiv]; simp only [max_def, min_def]; split_ifs <;> omega

private theorem roundRev_neg {lo up : ℕ} (hlo : 0 < lo) {x : ℤ} (hx : x < 0) :
    (if roundRev lo up .none x < 0 then 1 else 0) = 0 ∧
      (roundRev lo up .none x).natAbs = min (x.natAbs / 2) up := by
  unfold roundRev clampInt
  have hdiv : (x + 1) / 2 = -((x.natAbs / 2 : ℕ) : ℤ) := by omega
  rw [hdiv, neg_neg]; simp only [max_def, min_def]; split_ifs <;> omega

/-- Compute and store the forward/reverse rounded cost pair of a single edge `e`. -/
wram_def stage1RoundEdge (minIdx : ℕ)
    (fr, s, mag, loClip, upClip, pFS, pRS, pFM, pRM, e) {
  fSign := 0
  fMag := 0
  rSign := 0
  rMag := 0
  if fr == 0 {
    if s == 0 {
      q := (mag + 1) / 2
      fMag := minIdx(q, upClip)
      rMag := minIdx(q, loClip)
      rSign := minIdx(rMag, 1)
    } else {
      q := mag / 2
      fMag := minIdx(q, loClip)
      fSign := minIdx(fMag, 1)
      rMag := minIdx(q, upClip)
    }
  } else {
    if fr == 1 {
      fMag := upClip
      rSign := 1
      rMag := loClip
    } else {
      fSign := 1
      fMag := loClip
      rMag := upClip
    }
  }
  mem[pFS + e] := fSign
  mem[pRS + e] := rSign
  mem[pFM + e] := fMag
  mem[pRM + e] := rMag
  return 0
}

structure RoundEdgeIn where
  fr : FreezeState
  x : ℤ
  lo : ℕ
  up : ℕ
  e : ℕ
  oldFS : ℕ
  oldRS : ℕ
  oldFM : ℕ
  oldRM : ℕ

def stage1RoundEdgeSpec (w : ℕ) : Spec RoundEdgeIn where
  pre := fun g args => ⨆ (pFS : ℕ) (pRS : ℕ) (pFM : ℕ) (pRM : ℕ),
    ⌜args = [freezeCode g.fr, if g.x < 0 then 1 else 0, g.x.natAbs, g.lo, g.up,
        pFS, pRS, pFM, pRM, g.e] ∧
      g.x.natAbs + 1 < 2 ^ w ∧ 0 < g.lo ∧ g.lo ≤ g.up ∧ g.up < 2 ^ w ∧ 2 < 2 ^ w⌝ *
    Assn.list (pFS + g.e) [g.oldFS] * Assn.list (pRS + g.e) [g.oldRS] *
    Assn.list (pFM + g.e) [g.oldFM] * Assn.list (pRM + g.e) [g.oldRM]
  post := fun g args v => ⨆ (pFS : ℕ) (pRS : ℕ) (pFM : ℕ) (pRM : ℕ),
    ⌜args = [freezeCode g.fr, if g.x < 0 then 1 else 0, g.x.natAbs, g.lo, g.up,
        pFS, pRS, pFM, pRM, g.e] ∧ v = 0⌝ *
    Assn.list (pFS + g.e) [if roundFwd g.lo g.up g.fr g.x < 0 then 1 else 0] *
    Assn.list (pRS + g.e) [if roundRev g.lo g.up g.fr g.x < 0 then 1 else 0] *
    Assn.list (pFM + g.e) [(roundFwd g.lo g.up g.fr g.x).natAbs] *
    Assn.list (pRM + g.e) [(roundRev g.lo g.up g.fr g.x).natAbs]

theorem stage1RoundEdge_meets {w : ℕ} {p : Program} {f minIdx : ℕ}
    (hp : p.procs[f]? = some (stage1RoundEdge minIdx))
    (hmin : Meets w p minIdx ((stage1MinSpec w).withCost fun _ _ => 15)) :
    Meets w p f ((stage1RoundEdgeSpec w).withCost fun _ _ => 120) := by
  sep_enter g with hxfit hlo hle hup hw
  obtain ⟨fr, x, lo, up, e, oldFS, oldRS, oldFM, oldRM⟩ := g
  dsimp only at hxfit hlo hle hup hw ⊢
  have hup_pos : 0 < up := by omega
  cases fr with
  | none =>
    dsimp only [freezeCode]
    iterate 4 sep_step
    sep_step
    by_cases hneg : x < 0
    · simp only [hneg, ↓reduceIte]
      obtain ⟨hfs, hfm⟩ := roundFwd_neg (lo := lo) hup_pos hneg
      obtain ⟨hrs, hrm⟩ := roundRev_neg (up := up) hlo hneg
      sep_step
      sep_step; sep_step; sep_step
      sep_step from (x.natAbs / 2, lo)
      sep_step
      sep_step from (min (x.natAbs / 2) lo, 1)
      sep_step from (x.natAbs / 2, up)
      sep_run
    · have hnonneg : 0 ≤ x := Int.not_lt.mp hneg
      simp only [hneg, ↓reduceIte]
      obtain ⟨hfs, hfm⟩ := roundFwd_nonneg (up := up) hlo hnonneg
      obtain ⟨hrs, hrm⟩ := roundRev_nonneg (lo := lo) hup_pos hnonneg
      sep_step
      sep_step; sep_step; sep_step
      sep_step from ((x.natAbs + 1) / 2, up)
      sep_step
      sep_step from ((x.natAbs + 1) / 2, lo)
      sep_step from (min ((x.natAbs + 1) / 2) lo, 1)
      sep_run
  | pos =>
    dsimp only [freezeCode]
    iterate 4 sep_step
    sep_step; sep_step
    have h1 : (if roundFwd lo up .pos x < 0 then 1 else 0) = 0 := by
      unfold roundFwd; dsimp only; split_ifs <;> omega
    have h2 : (if roundRev lo up .pos x < 0 then 1 else 0) = 1 := by
      unfold roundRev; dsimp only; split_ifs <;> omega
    have h3 : (roundFwd lo up .pos x).natAbs = up := by unfold roundFwd; simp
    have h4 : (roundRev lo up .pos x).natAbs = lo := by unfold roundRev; simp
    sep_run
  | neg =>
    dsimp only [freezeCode]
    iterate 4 sep_step
    sep_step; sep_step
    have h1 : (if roundFwd lo up .neg x < 0 then 1 else 0) = 1 := by
      unfold roundFwd; dsimp only; split_ifs <;> omega
    have h2 : (if roundRev lo up .neg x < 0 then 1 else 0) = 0 := by
      unfold roundRev; dsimp only; split_ifs <;> omega
    have h3 : (roundFwd lo up .neg x).natAbs = lo := by unfold roundFwd; simp
    have h4 : (roundRev lo up .neg x).natAbs = up := by unfold roundRev; simp
    sep_run

/-! ### 2. Loop over all `m` edges (`stage1RoundedCosts`) -/

/-- Write the `2 * m` rounded residual edge costs `(pResCSign, pResCMag)` for one Stage 1
round from `(pFrozen, pHSign, pHMag)` and `(loClip, upClip)`. -/
wram_def stage1RoundedCosts (edgeIdx : ℕ)
    (m, pFrozen, pHSign, pHMag, loClip, upClip, pResCSign, pResCMag) {
  pRevS := pResCSign + m
  pRevM := pResCMag + m
  for e in 0 .. m {
    fr := mem[pFrozen + e]
    s := mem[pHSign + e]
    mag := mem[pHMag + e]
    r := edgeIdx(fr, s, mag, loClip, upClip, pResCSign, pRevS, pResCMag, pRevM, e)
    r := 0
  }
  return 0
}

private def fwdSList (m lo up : ℕ) (fr : Fin m → FreezeState) (x : Fin m → ℤ) : List ℕ :=
  List.ofFn fun e : Fin m => if roundFwd lo up (fr e) (x e) < 0 then 1 else 0

private def revSList (m lo up : ℕ) (fr : Fin m → FreezeState) (x : Fin m → ℤ) : List ℕ :=
  List.ofFn fun e : Fin m => if roundRev lo up (fr e) (x e) < 0 then 1 else 0

private def fwdMList (m lo up : ℕ) (fr : Fin m → FreezeState) (x : Fin m → ℤ) : List ℕ :=
  List.ofFn fun e : Fin m => (roundFwd lo up (fr e) (x e)).natAbs

private def revMList (m lo up : ℕ) (fr : Fin m → FreezeState) (x : Fin m → ℤ) : List ℕ :=
  List.ofFn fun e : Fin m => (roundRev lo up (fr e) (x e)).natAbs

private theorem narrowRoundedCosts_sign_eq (C : Circulation)
    (fr : Fin C.m → FreezeState) (x : Fin C.m → ℤ) :
    (List.ofFn fun a : Fin (C.m + C.m) =>
      if narrowRoundedCosts C fr x a < 0 then 1 else 0) =
    fwdSList C.m (lowerClip C.m) (upperClip C.m) fr x ++
      revSList C.m (lowerClip C.m) (upperClip C.m) fr x := by
  unfold fwdSList revSList
  refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
  have hi1' : i < C.m + C.m := by simpa using hi1
  simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
  unfold narrowRoundedCosts
  by_cases h : i < C.m
  · simp only [h, ↓reduceDIte]
    have heq : (⟨i, hi1'⟩ : Fin (C.m + C.m)) = Fin.castAdd C.m ⟨i, h⟩ := by ext; rfl
    rw [heq, Fin.addCases_left]; rfl
  · simp only [h, ↓reduceDIte]
    have hi' : i - C.m < C.m := by omega
    have heq : (⟨i, hi1'⟩ : Fin (C.m + C.m)) = Fin.natAdd C.m ⟨i - C.m, hi'⟩ := by
      ext; simp; omega
    rw [heq, Fin.addCases_right]; rfl

private theorem narrowRoundedCosts_mag_eq (C : Circulation)
    (fr : Fin C.m → FreezeState) (x : Fin C.m → ℤ) :
    (List.ofFn fun a : Fin (C.m + C.m) => (narrowRoundedCosts C fr x a).natAbs) =
    fwdMList C.m (lowerClip C.m) (upperClip C.m) fr x ++
      revMList C.m (lowerClip C.m) (upperClip C.m) fr x := by
  unfold fwdMList revMList
  refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
  have hi1' : i < C.m + C.m := by simpa using hi1
  simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
  unfold narrowRoundedCosts
  by_cases h : i < C.m
  · simp only [h, ↓reduceDIte]
    have heq : (⟨i, hi1'⟩ : Fin (C.m + C.m)) = Fin.castAdd C.m ⟨i, h⟩ := by ext; rfl
    rw [heq, Fin.addCases_left]; rfl
  · simp only [h, ↓reduceDIte]
    have hi' : i - C.m < C.m := by omega
    have heq : (⟨i, hi1'⟩ : Fin (C.m + C.m)) = Fin.natAdd C.m ⟨i - C.m, hi'⟩ := by
      ext; simp; omega
    rw [heq, Fin.addCases_right]; rfl

private def roundOutCell (m pFS pFM : ℕ) (fS rS fM rM oS1 oS2 oM1 oM2 : List ℕ) (e i : ℕ) : Assn :=
  Assn.list (pFS + i) [if i < e then fS.getD i 0 else oS1.getD i 0] *
  Assn.list (pFS + m + i) [if i < e then rS.getD i 0 else oS2.getD i 0] *
  Assn.list (pFM + i) [if i < e then fM.getD i 0 else oM1.getD i 0] *
  Assn.list (pFM + m + i) [if i < e then rM.getD i 0 else oM2.getD i 0]

private theorem roundOutCell_init {m pFS pFM : ℕ} {fS rS fM rM oldSign oldMag : List ℕ}
    (hlenS : oldSign.length = 2 * m) (hlenM : oldMag.length = 2 * m) :
    Assn.list pFS oldSign * Assn.list pFM oldMag =
      ∏ i ∈ Finset.range m, roundOutCell m pFS pFM fS rS fM rM
        (oldSign.take m) (oldSign.drop m) (oldMag.take m) (oldMag.drop m) 0 i := by
  have hS1 : (oldSign.take m).length = m := by simp [hlenS]; omega
  have hS2 : (oldSign.drop m).length = m := by simp [hlenS]; omega
  have hM1 : (oldMag.take m).length = m := by simp [hlenM]; omega
  have hM2 : (oldMag.drop m).length = m := by simp [hlenM]; omega
  have hsplitS : Assn.list pFS oldSign =
      Assn.list pFS (oldSign.take m) * Assn.list (pFS + m) (oldSign.drop m) := by
    conv_lhs => rw [← List.take_append_drop m oldSign]
    rw [Assn.list_append, hS1]
  have hsplitM : Assn.list pFM oldMag =
      Assn.list pFM (oldMag.take m) * Assn.list (pFM + m) (oldMag.drop m) := by
    conv_lhs => rw [← List.take_append_drop m oldMag]
    rw [Assn.list_append, hM1]
  rw [hsplitS, hsplitM,
    list_eq_prod_singleton pFS (oldSign.take m), list_eq_prod_singleton (pFS + m) (oldSign.drop m),
    list_eq_prod_singleton pFM (oldMag.take m), list_eq_prod_singleton (pFM + m) (oldMag.drop m),
    hS1, hS2, hM1, hM2]
  simp only [roundOutCell, Nat.not_lt_zero, ↓reduceIte, Finset.prod_mul_distrib, mul_assoc]

private theorem roundOutCell_final {m pFS pFM : ℕ} {fS rS fM rM oS1 oS2 oM1 oM2 : List ℕ}
    (hfS : fS.length = m) (hrS : rS.length = m) (hfM : fM.length = m) (hrM : rM.length = m) :
    (∏ i ∈ Finset.range m, roundOutCell m pFS pFM fS rS fM rM oS1 oS2 oM1 oM2 m i) =
      Assn.list pFS (fS ++ rS) * Assn.list pFM (fM ++ rM) := by
  have hcongr : (∏ i ∈ Finset.range m, roundOutCell m pFS pFM fS rS fM rM oS1 oS2 oM1 oM2 m i) =
      ∏ i ∈ Finset.range m,
        (Assn.list (pFS + i) [fS.getD i 0] * Assn.list (pFS + m + i) [rS.getD i 0] *
         Assn.list (pFM + i) [fM.getD i 0] * Assn.list (pFM + m + i) [rM.getD i 0]) :=
    Finset.prod_congr rfl fun i hi => by
      simp only [roundOutCell, Finset.mem_range.mp hi, ↓reduceIte]
  rw [hcongr]
  simp only [Finset.prod_mul_distrib]
  rw [Assn.list_append, Assn.list_append, hfS, hfM,
    list_eq_prod_singleton pFS fS, list_eq_prod_singleton (pFS + m) rS,
    list_eq_prod_singleton pFM fM, list_eq_prod_singleton (pFM + m) rM,
    hfS, hrS, hfM, hrM]
  simp only [mul_assoc]

private theorem roundOutCell_step {m pFS pFM : ℕ} {fS rS fM rM oS1 oS2 oM1 oM2 : List ℕ}
    {e : ℕ} (he : e < m) :
    Assn.list (pFS + e) [fS.getD e 0] * Assn.list (pFS + m + e) [rS.getD e 0] *
    Assn.list (pFM + e) [fM.getD e 0] * Assn.list (pFM + m + e) [rM.getD e 0] *
    (∏ i ∈ (Finset.range m).erase e, roundOutCell m pFS pFM fS rS fM rM oS1 oS2 oM1 oM2 e i) =
      ∏ i ∈ Finset.range m, roundOutCell m pFS pFM fS rS fM rM oS1 oS2 oM1 oM2 (e + 1) i := by
  have hmem : e ∈ Finset.range m := Finset.mem_range.mpr he
  rw [Assn.prod_eq_mul_erase hmem (roundOutCell m pFS pFM fS rS fM rM oS1 oS2 oM1 oM2 (e + 1))]
  congr 1
  · simp [roundOutCell]
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ e := (Finset.mem_erase.mp hi).1
    have hiff : (i < e) ↔ (i < e + 1) := by omega
    simp only [roundOutCell, hiff]

private structure RoundedGenIn where
  m : ℕ
  lo : ℕ
  up : ℕ
  fr : Fin m → FreezeState
  x : Fin m → ℤ
  oldSign : List ℕ
  oldMag : List ℕ

private def stage1RoundedCostsGenSpec (w : ℕ) : Spec RoundedGenIn where
  pre := fun g args =>
    ⨆ (pFrozen : ℕ) (pHSign : ℕ) (pHMag : ℕ) (pResCSign : ℕ) (pResCMag : ℕ),
      ⌜args = [g.m, pFrozen, pHSign, pHMag, g.lo, g.up, pResCSign, pResCMag] ∧
        g.oldSign.length = 2 * g.m ∧ g.oldMag.length = 2 * g.m ∧
        (∀ e : Fin g.m, (g.x e).natAbs + 1 < 2 ^ w) ∧
        0 < g.lo ∧ g.lo ≤ g.up ∧ g.up < 2 ^ w ∧ 2 < 2 ^ w⌝ *
      Assn.list pFrozen (List.ofFn fun e : Fin g.m => freezeCode (g.fr e)) *
      Assn.list pHSign (List.ofFn fun e : Fin g.m => if g.x e < 0 then 1 else 0) *
      Assn.list pHMag (List.ofFn fun e : Fin g.m => (g.x e).natAbs) *
      Assn.list pResCSign g.oldSign *
      Assn.list pResCMag g.oldMag
  post := fun g args v =>
    ⨆ (pFrozen : ℕ) (pHSign : ℕ) (pHMag : ℕ) (pResCSign : ℕ) (pResCMag : ℕ),
      ⌜args = [g.m, pFrozen, pHSign, pHMag, g.lo, g.up, pResCSign, pResCMag] ∧ v = 0⌝ *
      Assn.list pFrozen (List.ofFn fun e : Fin g.m => freezeCode (g.fr e)) *
      Assn.list pHSign (List.ofFn fun e : Fin g.m => if g.x e < 0 then 1 else 0) *
      Assn.list pHMag (List.ofFn fun e : Fin g.m => (g.x e).natAbs) *
      Assn.list pResCSign (fwdSList g.m g.lo g.up g.fr g.x ++ revSList g.m g.lo g.up g.fr g.x) *
      Assn.list pResCMag (fwdMList g.m g.lo g.up g.fr g.x ++ revMList g.m g.lo g.up g.fr g.x)

private theorem stage1RoundedCostsGen_meets {w : ℕ} {p : Program} {f edgeIdx : ℕ}
    (hp : p.procs[f]? = some (stage1RoundedCosts edgeIdx))
    (hedge : Meets w p edgeIdx ((stage1RoundEdgeSpec w).withCost fun _ _ => 120)) :
    Meets w p f ((stage1RoundedCostsGenSpec w).withCost fun g _ => 170 * g.m + 30) := by
  sep_enter g with hlenS hlenM hxfit hlo_pos hlo_le hup hw
  obtain ⟨m, lo, up, fr, x, oldSign, oldMag⟩ := g
  dsimp only at hlenS hlenM hxfit hlo_pos hlo_le hup hw ⊢
  have hfrL_len : (List.ofFn fun e : Fin m => freezeCode (fr e)).length = m := List.length_ofFn
  have hsL_len : (List.ofFn fun e : Fin m => if x e < 0 then 1 else 0).length = m := List.length_ofFn
  have hmL_len : (List.ofFn fun e : Fin m => (x e).natAbs).length = m := List.length_ofFn
  have hfwdS_len : (fwdSList m lo up fr x).length = m := List.length_ofFn
  have hrevS_len : (revSList m lo up fr x).length = m := List.length_ofFn
  have hfwdM_len : (fwdMList m lo up fr x).length = m := List.length_ofFn
  have hrevM_len : (revMList m lo up fr x).length = m := List.length_ofFn
  have hfrL_get : ∀ e (he : e < m), (List.ofFn fun i : Fin m => freezeCode (fr i)).getD e 0 =
      freezeCode (fr ⟨e, he⟩) := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  have hsL_get : ∀ e (he : e < m), (List.ofFn fun i : Fin m => if x i < 0 then 1 else 0).getD e 0 =
      (if x ⟨e, he⟩ < 0 then 1 else 0) := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  have hmL_get : ∀ e (he : e < m), (List.ofFn fun i : Fin m => (x i).natAbs).getD e 0 =
      (x ⟨e, he⟩).natAbs := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  have hfS_get : ∀ e (he : e < m), (fwdSList m lo up fr x).getD e 0 =
      (if roundFwd lo up (fr ⟨e, he⟩) (x ⟨e, he⟩) < 0 then 1 else 0) := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp [fwdSList]; omega)]; exact List.getElem_ofFn ..
  have hrS_get : ∀ e (he : e < m), (revSList m lo up fr x).getD e 0 =
      (if roundRev lo up (fr ⟨e, he⟩) (x ⟨e, he⟩) < 0 then 1 else 0) := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp [revSList]; omega)]; exact List.getElem_ofFn ..
  have hfM_get : ∀ e (he : e < m), (fwdMList m lo up fr x).getD e 0 =
      (roundFwd lo up (fr ⟨e, he⟩) (x ⟨e, he⟩)).natAbs := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp [fwdMList]; omega)]; exact List.getElem_ofFn ..
  have hrM_get : ∀ e (he : e < m), (revMList m lo up fr x).getD e 0 =
      (roundRev lo up (fr ⟨e, he⟩) (x ⟨e, he⟩)).natAbs := fun e he => by
    rw [List.getD_eq_getElem _ _ (by simp [revMList]; omega)]; exact List.getElem_ofFn ..
  generalize hfrL_eq : (List.ofFn fun e : Fin m => freezeCode (fr e)) = frL at hfrL_len hfrL_get ⊢
  generalize hsL_eq : (List.ofFn fun e : Fin m => if x e < 0 then 1 else 0) = sL at hsL_len hsL_get ⊢
  generalize hmL_eq : (List.ofFn fun e : Fin m => (x e).natAbs) = mL at hmL_len hmL_get ⊢
  generalize hfS_eq : fwdSList m lo up fr x = fS at hfwdS_len hfS_get ⊢
  generalize hrS_eq : revSList m lo up fr x = rS at hrevS_len hrS_get ⊢
  generalize hfM_eq : fwdMList m lo up fr x = fM at hfwdM_len hfM_get ⊢
  generalize hrM_eq : revMList m lo up fr x = rM at hrevM_len hrM_get ⊢
  sep_step; sep_step
  sep_apply roundOutCell_init (fS := fS) (rS := rS) (fM := fM) (rM := rM) hlenS hlenM
  set oS1 := oldSign.take m
  set oS2 := oldSign.drop m
  set oM1 := oldMag.take m
  set oM2 := oldMag.drop m
  sep_for (fun e (t : ℕ × ℕ × ℕ × ℕ) =>
    ⟨[m, pFrozen, pHSign, pHMag, lo, up, pResCSign, pResCMag,
      pResCSign + m, pResCMag + m, e, t.1, t.2.1, t.2.2.1, t.2.2.2],
      e ≤ m, 160 * (m - e) + 5,
      [Assn.list pFrozen frL,
       Assn.list pHSign sL,
       Assn.list pHMag mL,
       ∏ i ∈ Finset.range m, roundOutCell m pResCSign pResCMag fS rS fM rM oS1 oS2 oM1 oM2 e i]⟩)
    with ⟨t0, t1, t2, t3⟩
  · have hxe := hxfit ⟨e, hhi⟩
    have hmem : e ∈ Finset.range m := Finset.mem_range.mpr hhi
    have hfr_e : frL[e]'(by omega) = freezeCode (fr ⟨e, hhi⟩) := by
      rw [← List.getD_eq_getElem _ _ (by omega)]; exact hfrL_get e hhi
    have hs_e : sL[e]'(by omega) = (if x ⟨e, hhi⟩ < 0 then 1 else 0) := by
      rw [← List.getD_eq_getElem _ _ (by omega)]; exact hsL_get e hhi
    have hmag_e : mL[e]'(by omega) = (x ⟨e, hhi⟩).natAbs := by
      rw [← List.getD_eq_getElem _ _ (by omega)]; exact hmL_get e hhi
    sep_step; sep_step; sep_step
    rw [hfr_e, hs_e, hmag_e]
    sep_apply Assn.prod_eq_mul_erase hmem
      (roundOutCell m pResCSign pResCMag fS rS fM rM oS1 oS2 oM1 oM2 e)
    have hpop : roundOutCell m pResCSign pResCMag fS rS fM rM oS1 oS2 oM1 oM2 e e =
        Assn.list (pResCSign + e) [oS1.getD e 0] *
        Assn.list (pResCSign + m + e) [oS2.getD e 0] *
        Assn.list (pResCMag + e) [oM1.getD e 0] *
        Assn.list (pResCMag + m + e) [oM2.getD e 0] := by
      simp [roundOutCell]
    sep_apply hpop
    sep_step from ⟨fr ⟨e, hhi⟩, x ⟨e, hhi⟩, lo, up, e,
      oS1.getD e 0, oS2.getD e 0, oM1.getD e 0, oM2.getD e 0⟩
    rw [← hfS_get e hhi, ← hrS_get e hhi, ← hfM_get e hhi, ← hrM_get e hhi]
    sep_apply roundOutCell_step (pFS := pResCSign) (pFM := pResCMag)
      (fS := fS) (rS := rS) (fM := fM) (rM := rM)
      (oS1 := oS1) (oS2 := oS2) (oM1 := oM1) (oM2 := oM2) hhi
    sep_run
  · sep_apply roundOutCell_final (pFS := pResCSign) (pFM := pResCMag)
      (oS1 := oS1) (oS2 := oS2) (oM1 := oM1) (oM2 := oM2)
      hfwdS_len hrevS_len hfwdM_len hrevM_len
    rw [← hfrL_eq, ← hsL_eq, ← hmL_eq, ← hfS_eq, ← hrS_eq, ← hfM_eq, ← hrM_eq]
    sep_run

/-- Ghost input bundle for `stage1RoundedCostsSpec`. -/
structure Stage1RoundedCostsIn where
  C : Circulation
  fr : Fin C.m → FreezeState
  x : Fin C.m → ℤ
  oldSign : List ℕ
  oldMag : List ℕ

/-- Specification of `stage1RoundedCosts`. -/
def stage1RoundedCostsSpec (w : ℕ) : Spec Stage1RoundedCostsIn where
  pre := fun inp args =>
    ⨆ (pFrozen : ℕ) (pHSign : ℕ) (pHMag : ℕ) (pResCSign : ℕ) (pResCMag : ℕ),
      ⌜args = [inp.C.m, pFrozen, pHSign, pHMag, lowerClip inp.C.m, upperClip inp.C.m,
          pResCSign, pResCMag] ∧
        inp.oldSign.length = 2 * inp.C.m ∧ inp.oldMag.length = 2 * inp.C.m ∧
        (∀ e : Fin inp.C.m, (inp.x e).natAbs + 1 < 2 ^ w) ∧
        2 < 2 ^ w ∧ upperClip inp.C.m < 2 ^ w⌝ *
      Assn.list pFrozen (List.ofFn fun e : Fin inp.C.m => freezeCode (inp.fr e)) *
      Assn.list pHSign (List.ofFn fun e : Fin inp.C.m => if inp.x e < 0 then 1 else 0) *
      Assn.list pHMag (List.ofFn fun e : Fin inp.C.m => (inp.x e).natAbs) *
      Assn.list pResCSign inp.oldSign *
      Assn.list pResCMag inp.oldMag
  post := fun inp args v =>
    ⨆ (pFrozen : ℕ) (pHSign : ℕ) (pHMag : ℕ) (pResCSign : ℕ) (pResCMag : ℕ),
      ⌜args = [inp.C.m, pFrozen, pHSign, pHMag, lowerClip inp.C.m, upperClip inp.C.m,
          pResCSign, pResCMag] ∧ v = 0⌝ *
      Assn.list pFrozen (List.ofFn fun e : Fin inp.C.m => freezeCode (inp.fr e)) *
      Assn.list pHSign (List.ofFn fun e : Fin inp.C.m => if inp.x e < 0 then 1 else 0) *
      Assn.list pHMag (List.ofFn fun e : Fin inp.C.m => (inp.x e).natAbs) *
      Assn.list pResCSign (List.ofFn fun a : Fin (inp.C.m + inp.C.m) =>
        if narrowRoundedCosts inp.C inp.fr inp.x a < 0 then 1 else 0) *
      Assn.list pResCMag (List.ofFn fun a : Fin (inp.C.m + inp.C.m) =>
        (narrowRoundedCosts inp.C inp.fr inp.x a).natAbs)

theorem stage1RoundedCosts_meets {w : ℕ} {p : Program} {f edgeIdx : ℕ}
    (hp : p.procs[f]? = some (stage1RoundedCosts edgeIdx))
    (hedge : Meets w p edgeIdx ((stage1RoundEdgeSpec w).withCost fun _ _ => 120)) :
    Meets w p f ((stage1RoundedCostsSpec w).withCost fun inp _ => 170 * inp.C.m + 30) := by
  refine (stage1RoundedCostsGen_meets (w := w) hp hedge).weaken fun inp args _ h c _ hpre => ?_
  refine ⟨⟨inp.C.m, lowerClip inp.C.m, upperClip inp.C.m,
      inp.fr, inp.x, inp.oldSign, inp.oldMag⟩, ?_, fun v => ?_⟩
  · refine (Assn.mul_le_mul_of_le ?_ le_rfl) h c hpre
    simp only [stage1RoundedCostsSpec, stage1RoundedCostsGenSpec]
    refine iSup_le fun pF => iSup_le fun pS => iSup_le fun pM =>
      iSup_le fun pRS => iSup_le fun pRM => ?_
    refine le_trans ?_ (le_iSup _ pF)
    refine le_trans ?_ (le_iSup _ pS)
    refine le_trans ?_ (le_iSup _ pM)
    refine le_trans ?_ (le_iSup _ pRS)
    refine le_trans ?_ (le_iSup _ pRM)
    refine Assn.mul_le_mul_of_le ?_ le_rfl
    refine Assn.mul_le_mul_of_le ?_ le_rfl
    refine Assn.mul_le_mul_of_le ?_ le_rfl
    refine Assn.mul_le_mul_of_le ?_ le_rfl
    refine Assn.mul_le_mul_of_le ?_ le_rfl
    intro h' c' ⟨⟨hargs, ha, hb, hc, hd, he⟩, hrest⟩
    exact ⟨⟨hargs, ha, hb, hc, Nat.two_pow_pos _, lowerClip_le_upperClip inp.C.m, he, hd⟩, hrest⟩
  · simp only [Spec.withCost, stage1RoundedCostsSpec, stage1RoundedCostsGenSpec]
    rw [← narrowRoundedCosts_sign_eq inp.C inp.fr inp.x,
        ← narrowRoundedCosts_mag_eq inp.C inp.fr inp.x]
    exact Assn.le_mul_gc _

theorem stage1RoundedCosts_meetsO {w : ℕ} {p : Program} {f edgeIdx : ℕ}
    (hp : p.procs[f]? = some (stage1RoundedCosts edgeIdx))
    (hedge : Meets w p edgeIdx ((stage1RoundEdgeSpec w).withCost fun _ _ => 120)) :
    MeetsO w p f (stage1RoundedCostsSpec w) fun inp _ => inp.C.m + 1 :=
  MeetsO.of_meets (stage1RoundedCosts_meets hp hedge) ⟨170, fun _ => by dsimp only; omega⟩

/-- Polymorphic module for `stage1Min`, `stage1RoundEdge`, and `stage1RoundedCosts`. -/
def stage1RoundedCostsMod {ι : Type} (name edgeName minName : ι) : Module ι :=
  ⟨[(minName, fun _ => stage1Min),
    (edgeName, fun idx => stage1RoundEdge (idx minName)),
    (name, fun idx => stage1RoundedCosts (idx edgeName))]⟩

theorem stage1RoundedCostsMod_noRand {ι : Type} (name edgeName minName : ι) :
    (stage1RoundedCostsMod name edgeName minName).NoRand := by
  wram_no_rand

theorem stage1RoundedCostsMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {name edgeName minName : ι}
    (hp : (stage1RoundedCostsMod name edgeName minName).Placed p idx) :
    MeetsO w p (idx name) (stage1RoundedCostsSpec w) fun inp _ => inp.C.m + 1 :=
  stage1RoundedCosts_meetsO
    (hp.get (n := name) (b := fun i => stage1RoundedCosts (i edgeName))
      (by simp [stage1RoundedCostsMod]))
    (stage1RoundEdge_meets
      (hp.get (n := edgeName) (b := fun i => stage1RoundEdge (i minName))
        (by simp [stage1RoundedCostsMod]))
      (stage1Min_meets (hp.get (n := minName) (b := fun _ => stage1Min)
        (by simp [stage1RoundedCostsMod]))))

end MinCostFlow.NarrowProg.Stage1
