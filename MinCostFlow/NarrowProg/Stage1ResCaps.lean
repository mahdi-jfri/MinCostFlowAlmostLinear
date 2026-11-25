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
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Residual capacity limb subtraction and canonical-length scanning (`stage1ResCaps`)

Computes the `2 * m` canonical residual capacity limb lengths for one Stage 1 round:
- `stage1CanonLen`: scans a `K_cap`-limb array and returns the canonical length (smallest prefix
  length whose suffix is all zeros) (`O(K_cap + 1)`).
- `stage1ResCaps`: for each edge `e ∈ 0 .. m`, computes `resFwd[e] = cap[e] - flow[e]` via
  `limbsSub` (borrow `0`) and records canonical lengths of `resFwd[e]` and `flow[e]` at
  `pResCapLens + e` and `pResCapLens + m + e` (`O(m * (K_cap + 1) + 1)`).
- `stage1ResCaps_split_for_bitScale`: splits `pResFwdBuf` and `pFlow` into their canonical
  prefixes (ready for `stage1BitScaleSpec`) plus zero-filled suffixes framed across `bitScale`.
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

/-! ### 1. Canonical length scanner (`stage1CanonLen`) -/

/-- Pure specification of the canonical prefix length of `xs.take i`. -/
def canonLenAux (xs : List ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if 0 < xs.getD i 0 then i + 1 else canonLenAux xs i

/-- Canonical limb length of a fixed-width limb list `xs`. -/
def canonLen (xs : List ℕ) : ℕ := canonLenAux xs xs.length

theorem canonLenAux_le (xs : List ℕ) (i : ℕ) : canonLenAux xs i ≤ i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    unfold canonLenAux
    split_ifs <;> omega

theorem canonLen_le (xs : List ℕ) : canonLen xs ≤ xs.length :=
  canonLenAux_le xs xs.length

theorem canonLenAux_zero_above (xs : List ℕ) :
    ∀ i j, canonLenAux xs i ≤ j → j < i → xs.getD j 0 = 0 := by
  intro i
  induction i with
  | zero => intro _ _ hlt; omega
  | succ i ih =>
    intro j hge hlt
    unfold canonLenAux at hge
    split_ifs at hge with hpos
    · omega
    · by_cases hji : j = i
      · subst hji; omega
      · exact ih j hge (by omega)

theorem canonLenAux_last_pos (xs : List ℕ) :
    ∀ i, 0 < canonLenAux xs i → 0 < xs.getD (canonLenAux xs i - 1) 0 := by
  intro i
  induction i with
  | zero => simp [canonLenAux]
  | succ i ih =>
    unfold canonLenAux
    split_ifs with hpos
    · intro _; simpa using hpos
    · exact ih

theorem drop_canonLen_eq_replicate (xs : List ℕ) :
    xs.drop (canonLen xs) = List.replicate (xs.length - canonLen xs) 0 := by
  have hle := canonLen_le xs
  refine List.ext_getElem (by simp) fun j hj1 hj2 => ?_
  simp only [List.getElem_drop, List.getElem_replicate]
  have hlt : canonLen xs + j < xs.length := by simp at hj1; omega
  have hge : canonLenAux xs xs.length ≤ canonLen xs + j := by unfold canonLen; omega
  have hz := canonLenAux_zero_above xs xs.length (canonLen xs + j) hge hlt
  rwa [List.getD_eq_getElem _ _ hlt] at hz

theorem canonicalLimbs_take_canonLen {k : ℕ} {xs : List ℕ} (hL : Limbs k xs) :
    CanonicalLimbs k (xs.take (canonLen xs)) := by
  have hle := canonLen_le xs
  refine ⟨fun x hx => hL x (List.mem_of_mem_take hx), fun hne => ?_⟩
  have hlen : (xs.take (canonLen xs)).length = canonLen xs := by simp [hle]
  have hpos : 0 < canonLen xs := by
    by_contra h0
    have h0' : canonLen xs = 0 := by omega
    rw [h0', List.take_zero] at hne
    exact hne rfl
  have hlast : (xs.take (canonLen xs)).getLast hne = xs.getD (canonLen xs - 1) 0 := by
    rw [List.getLast_eq_getElem, List.getElem_take]
    simp only [hlen]
    have hlt : canonLen xs - 1 < xs.length := by omega
    exact (List.getD_eq_getElem xs 0 hlt).symm
  rw [hlast]
  exact Nat.ne_of_gt (canonLenAux_last_pos xs xs.length hpos)

theorem ofDigits_take_canonLen (b : ℕ) (xs : List ℕ) :
    Nat.ofDigits b (xs.take (canonLen xs)) = Nat.ofDigits b xs := by
  conv_rhs => rw [← List.take_append_drop (canonLen xs) xs, drop_canonLen_eq_replicate]
  exact (ofDigits_append_replicate_zero b _ _).symm

/-- Scan `K_cap` limbs at `ptr` and return the canonical prefix length `canonLen xs`. -/
wram_def stage1CanonLen (ptr, K_cap) {
  lastNz := 0
  for i in 0 .. K_cap {
    v := mem[ptr + i]
    if 0 < v {
      lastNz := i + 1
    }
  }
  return lastNz
}

def stage1CanonLenSpec (w : ℕ) : Spec (List ℕ) where
  pre := fun xs args => ⨆ ptr : ℕ,
    ⌜args = [ptr, xs.length] ∧ xs.length < 2 ^ w ∧ 1 < 2 ^ w⌝ *
    Assn.list ptr xs
  post := fun xs args v => ⨆ ptr : ℕ,
    ⌜args = [ptr, xs.length] ∧ v = canonLen xs⌝ *
    Assn.list ptr xs

theorem stage1CanonLen_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1CanonLen) :
    Meets w p f ((stage1CanonLenSpec w).withCost fun xs _ => 50 * xs.length + 20) := by
  sep_enter xs with hlen hw
  sep_step
  sep_for (fun i (v : ℕ) =>
    ⟨[ptr, xs.length, canonLenAux xs i, i, v],
      i ≤ xs.length, 35 * (xs.length - i) + 5,
      [Assn.list ptr xs]⟩) with v
  · have hget : xs[i]'(by omega) = xs.getD i 0 := (List.getD_eq_getElem xs 0 (by omega)).symm
    have hle_i : canonLenAux xs i ≤ i := canonLenAux_le xs i
    sep_step
    by_cases hpos : 0 < xs.getD i 0
    · sep_step
      · simp only [canonLenAux, hpos, ↓reduceIte]
        sep_run
    · sep_step
      · simp only [canonLenAux, hpos, ↓reduceIte]
        sep_run
  · sep_run

/-! ### 2. Residual capacity computation (`stage1ResCaps`) -/

/-- Compute `resFwd[e] = cap[e] - flow[e]` and canonical lengths of `resFwd[e]` and `flow[e]`
for all `e ∈ 0 .. m`. -/
wram_def stage1ResCaps (subIdx canonIdx : ℕ)
    (m, k, K_cap, pCapBuf, pFlow, pResFwdBuf, pResCapLens) {
  cPtr := pCapBuf
  fPtr := pFlow
  rPtr := pResFwdBuf
  for e in 0 .. m {
    b := subIdx(cPtr, fPtr, rPtr, K_cap, k)
    l1 := canonIdx(rPtr, K_cap)
    mem[pResCapLens + e] := l1
    l2 := canonIdx(fPtr, K_cap)
    mem[pResCapLens + m + e] := l2
    cPtr := cPtr + K_cap
    fPtr := fPtr + K_cap
    rPtr := rPtr + K_cap
  }
  return 0
}

structure Stage1ResCapsIn where
  m : ℕ
  k : ℕ
  K_cap : ℕ
  cap : Fin m → ℕ
  capLimbs : Fin m → List ℕ
  flow : Fin m → ℕ
  flowLimbs : Fin m → List ℕ
  oldResFwd : Fin m → List ℕ
  oldLens : List ℕ

private theorem ofDigits_lt_pow_res {k : ℕ} {l : List ℕ} (hL : Limbs k l) :
    Nat.ofDigits (2 ^ k) l < 2 ^ (k * l.length) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [Nat.ofDigits_cons, List.length_cons]
    have hd : d < 2 ^ k := hL d List.mem_cons_self
    have hds : Nat.ofDigits (2 ^ k) ds < 2 ^ (k * ds.length) :=
      ih fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have hpow : 2 ^ (k * (ds.length + 1)) = 2 ^ k * 2 ^ (k * ds.length) := by
      rw [Nat.mul_add, Nat.mul_one, pow_add, mul_comm]
    rw [hpow]
    calc d + 2 ^ k * Nat.ofDigits (2 ^ k) ds
        < 2 ^ k + 2 ^ k * Nat.ofDigits (2 ^ k) ds := Nat.add_lt_add_right hd _
      _ = 2 ^ k * (Nat.ofDigits (2 ^ k) ds + 1) := by ring
      _ ≤ 2 ^ k * 2 ^ (k * ds.length) := Nat.mul_le_mul_left _ hds

private theorem subLimbs_res_spec {k K_cap : ℕ} (hk : 1 ≤ k)
    {cL fL : List ℕ} {c f : ℕ}
    (hcL : Limbs k cL) (hfL : Limbs k fL)
    (hclen : cL.length = K_cap) (hflen : fL.length = K_cap)
    (hcv : Nat.ofDigits (2 ^ k) cL = c) (hfv : Nat.ofDigits (2 ^ k) fL = f)
    (hle : f ≤ c) :
    Limbs k (subLimbs k cL fL) ∧ (subLimbs k cL fL).length = K_cap ∧
      Nat.ofDigits (2 ^ k) (subLimbs k cL fL) = c - f := by
  obtain ⟨hsub_eq, _, hsub_L⟩ := subRun_spec hk hcL hfL (by omega) cL.length le_rfl
  rw [List.take_length, List.take_of_length_le (by omega), hcv, hfv] at hsub_eq
  have hbor0 : (carryRun (subStep k cL fL) cL.length).2 = 0 := by
    by_contra hne
    have hge1 : 1 ≤ (carryRun (subStep k cL fL) cL.length).2 := by omega
    have hlt : Nat.ofDigits (2 ^ k) (carryRun (subStep k cL fL) cL.length).1 < (2 ^ k) ^ K_cap := by
      have h1 := ofDigits_lt_pow_res hsub_L
      rw [length_carryRun, hclen, pow_mul] at h1
      rwa [hclen]
    have hpow : (2 ^ k) ^ cL.length = (2 ^ k) ^ K_cap := by rw [hclen]
    have hmul : (2 ^ k) ^ cL.length ≤
        (carryRun (subStep k cL fL) cL.length).2 * (2 ^ k) ^ cL.length := by
      simpa using Nat.mul_le_mul_right ((2 ^ k) ^ cL.length) hge1
    omega
  refine ⟨hsub_L, ?_, ?_⟩
  · unfold subLimbs; rw [length_carryRun, hclen]
  · unfold subLimbs; rw [hbor0, Nat.zero_mul, Nat.add_zero] at hsub_eq; omega

def stage1ResCapsSpec (w : ℕ) : Spec Stage1ResCapsIn where
  pre := fun g args =>
    ⨆ (pCapBuf : ℕ) (pFlow : ℕ) (pResFwdBuf : ℕ) (pResCapLens : ℕ),
      ⌜args = [g.m, g.k, g.K_cap, pCapBuf, pFlow, pResFwdBuf, pResCapLens] ∧
        1 ≤ g.k ∧ 2 * g.k ≤ w ∧ g.K_cap < 2 ^ w ∧
        g.oldLens.length = 2 * g.m ∧
        pCapBuf + g.m * g.K_cap < 2 ^ w ∧
        pFlow + g.m * g.K_cap < 2 ^ w ∧
        pResFwdBuf + g.m * g.K_cap < 2 ^ w ∧
        (∀ e : Fin g.m, Limbs g.k (g.capLimbs e) ∧ (g.capLimbs e).length = g.K_cap ∧
          Nat.ofDigits (2 ^ g.k) (g.capLimbs e) = g.cap e) ∧
        (∀ e : Fin g.m, Limbs g.k (g.flowLimbs e) ∧ (g.flowLimbs e).length = g.K_cap ∧
          Nat.ofDigits (2 ^ g.k) (g.flowLimbs e) = g.flow e ∧ g.flow e ≤ g.cap e) ∧
        (∀ e : Fin g.m, (g.oldResFwd e).length = g.K_cap)⌝ *
      (∏ e ∈ Finset.range g.m, Assn.list (pCapBuf + e * g.K_cap)
        (if h : e < g.m then g.capLimbs ⟨e, h⟩ else [])) *
      (∏ e ∈ Finset.range g.m, Assn.list (pFlow + e * g.K_cap)
        (if h : e < g.m then g.flowLimbs ⟨e, h⟩ else [])) *
      (∏ e ∈ Finset.range g.m, Assn.list (pResFwdBuf + e * g.K_cap)
        (if h : e < g.m then g.oldResFwd ⟨e, h⟩ else [])) *
      Assn.list pResCapLens g.oldLens
  post := fun g args v =>
    ⨆ (pCapBuf : ℕ) (pFlow : ℕ) (pResFwdBuf : ℕ) (pResCapLens : ℕ),
      let resFwd : Fin g.m → List ℕ := fun e => subLimbs g.k (g.capLimbs e) (g.flowLimbs e)
      let fwdLens := List.ofFn fun e : Fin g.m => canonLen (resFwd e)
      let revLens := List.ofFn fun e : Fin g.m => canonLen (g.flowLimbs e)
      ⌜args = [g.m, g.k, g.K_cap, pCapBuf, pFlow, pResFwdBuf, pResCapLens] ∧ v = 0 ∧
        (∀ e : Fin g.m, Limbs g.k (resFwd e) ∧ (resFwd e).length = g.K_cap ∧
          Nat.ofDigits (2 ^ g.k) (resFwd e) = g.cap e - g.flow e)⌝ *
      (∏ e ∈ Finset.range g.m, Assn.list (pCapBuf + e * g.K_cap)
        (if h : e < g.m then g.capLimbs ⟨e, h⟩ else [])) *
      (∏ e ∈ Finset.range g.m, Assn.list (pFlow + e * g.K_cap)
        (if h : e < g.m then g.flowLimbs ⟨e, h⟩ else [])) *
      (∏ e ∈ Finset.range g.m, Assn.list (pResFwdBuf + e * g.K_cap)
        (if h : e < g.m then resFwd ⟨e, h⟩ else [])) *
      Assn.list pResCapLens (fwdLens ++ revLens)

private def resCapCell (m K_cap pCapBuf pFlow pResFwdBuf pResCapLens : ℕ)
    (capL flowL oldR newR : Fin m → List ℕ)
    (oL1 oL2 fL rL : List ℕ) (e i : ℕ) : Assn :=
  Assn.list (pCapBuf + i * K_cap) (if h : i < m then capL ⟨i, h⟩ else []) *
  Assn.list (pFlow + i * K_cap) (if h : i < m then flowL ⟨i, h⟩ else []) *
  Assn.list (pResFwdBuf + i * K_cap)
    (if i < e then (if h : i < m then newR ⟨i, h⟩ else [])
     else (if h : i < m then oldR ⟨i, h⟩ else [])) *
  Assn.list (pResCapLens + i) [if i < e then fL.getD i 0 else oL1.getD i 0] *
  Assn.list (pResCapLens + m + i) [if i < e then rL.getD i 0 else oL2.getD i 0]

private theorem resCapCell_init {m K_cap pCapBuf pFlow pResFwdBuf pResCapLens : ℕ}
    {capL flowL oldR newR : Fin m → List ℕ} {oldLens fL rL : List ℕ}
    (hlen : oldLens.length = 2 * m) :
    (∏ i ∈ Finset.range m, Assn.list (pCapBuf + i * K_cap) (if h : i < m then capL ⟨i, h⟩ else [])) *
    (∏ i ∈ Finset.range m, Assn.list (pFlow + i * K_cap) (if h : i < m then flowL ⟨i, h⟩ else [])) *
    (∏ i ∈ Finset.range m, Assn.list (pResFwdBuf + i * K_cap) (if h : i < m then oldR ⟨i, h⟩ else [])) *
    Assn.list pResCapLens oldLens =
      ∏ i ∈ Finset.range m, resCapCell m K_cap pCapBuf pFlow pResFwdBuf pResCapLens
        capL flowL oldR newR (oldLens.take m) (oldLens.drop m) fL rL 0 i := by
  have h1 : (oldLens.take m).length = m := by simp [hlen]; omega
  have h2 : (oldLens.drop m).length = m := by simp [hlen]; omega
  have hsplit : Assn.list pResCapLens oldLens =
      Assn.list pResCapLens (oldLens.take m) * Assn.list (pResCapLens + m) (oldLens.drop m) := by
    conv_lhs => rw [← List.take_append_drop m oldLens]
    rw [Assn.list_append, h1]
  rw [hsplit, list_eq_prod_singleton pResCapLens (oldLens.take m),
    list_eq_prod_singleton (pResCapLens + m) (oldLens.drop m), h1, h2]
  simp only [resCapCell, Nat.not_lt_zero, ↓reduceIte, Finset.prod_mul_distrib, mul_assoc]

private theorem resCapCell_final {m K_cap pCapBuf pFlow pResFwdBuf pResCapLens : ℕ}
    {capL flowL oldR newR : Fin m → List ℕ} {oL1 oL2 fL rL : List ℕ}
    (hf : fL.length = m) (hr : rL.length = m) :
    (∏ i ∈ Finset.range m, resCapCell m K_cap pCapBuf pFlow pResFwdBuf pResCapLens
        capL flowL oldR newR oL1 oL2 fL rL m i) =
      (∏ i ∈ Finset.range m, Assn.list (pCapBuf + i * K_cap) (if h : i < m then capL ⟨i, h⟩ else [])) *
      (∏ i ∈ Finset.range m, Assn.list (pFlow + i * K_cap) (if h : i < m then flowL ⟨i, h⟩ else [])) *
      (∏ i ∈ Finset.range m, Assn.list (pResFwdBuf + i * K_cap) (if h : i < m then newR ⟨i, h⟩ else [])) *
      Assn.list pResCapLens (fL ++ rL) := by
  have hcongr :
      (∏ i ∈ Finset.range m, resCapCell m K_cap pCapBuf pFlow pResFwdBuf pResCapLens
          capL flowL oldR newR oL1 oL2 fL rL m i) =
      ∏ i ∈ Finset.range m,
        (Assn.list (pCapBuf + i * K_cap) (if h : i < m then capL ⟨i, h⟩ else []) *
         Assn.list (pFlow + i * K_cap) (if h : i < m then flowL ⟨i, h⟩ else []) *
         Assn.list (pResFwdBuf + i * K_cap) (if h : i < m then newR ⟨i, h⟩ else []) *
         Assn.list (pResCapLens + i) [fL.getD i 0] *
         Assn.list (pResCapLens + m + i) [rL.getD i 0]) :=
    Finset.prod_congr rfl fun i hi => by simp only [resCapCell, Finset.mem_range.mp hi, ↓reduceIte]
  rw [hcongr]
  simp only [Finset.prod_mul_distrib]
  rw [Assn.list_append, hf, list_eq_prod_singleton pResCapLens fL,
    list_eq_prod_singleton (pResCapLens + m) rL, hf, hr]
  simp only [mul_assoc]

private theorem resCapCell_step {m K_cap pCapBuf pFlow pResFwdBuf pResCapLens : ℕ}
    {capL flowL oldR newR : Fin m → List ℕ} {oL1 oL2 fL rL : List ℕ} {e : ℕ} (he : e < m) :
    Assn.list (pCapBuf + e * K_cap) (capL ⟨e, he⟩) *
    Assn.list (pFlow + e * K_cap) (flowL ⟨e, he⟩) *
    Assn.list (pResFwdBuf + e * K_cap) (newR ⟨e, he⟩) *
    Assn.list (pResCapLens + e) [fL.getD e 0] *
    Assn.list (pResCapLens + m + e) [rL.getD e 0] *
    (∏ i ∈ (Finset.range m).erase e, resCapCell m K_cap pCapBuf pFlow pResFwdBuf pResCapLens
        capL flowL oldR newR oL1 oL2 fL rL e i) =
      ∏ i ∈ Finset.range m, resCapCell m K_cap pCapBuf pFlow pResFwdBuf pResCapLens
        capL flowL oldR newR oL1 oL2 fL rL (e + 1) i := by
  have hmem : e ∈ Finset.range m := Finset.mem_range.mpr he
  rw [Assn.prod_eq_mul_erase hmem
    (resCapCell m K_cap pCapBuf pFlow pResFwdBuf pResCapLens
      capL flowL oldR newR oL1 oL2 fL rL (e + 1))]
  congr 1
  · simp [resCapCell, he]
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ e := (Finset.mem_erase.mp hi).1
    have hiff : (i < e) ↔ (i < e + 1) := by omega
    simp only [resCapCell, hiff]

theorem stage1ResCaps_meets {w : ℕ} {p : Program} {f subIdx canonIdx : ℕ} {Tsub : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage1ResCaps subIdx canonIdx))
    (hsub : Meets w p subIdx ((limbsSubSpec w).withCost fun x _ => Tsub x.2.1.length))
    (hsub_mono : ∀ n, Tsub n ≤ 200 * n + 100)
    (hcan : Meets w p canonIdx ((stage1CanonLenSpec w).withCost fun xs _ => 50 * xs.length + 20)) :
    Meets w p f ((stage1ResCapsSpec w).withCost fun g _ => (320 * g.K_cap + 230) * g.m + 40) := by
  sep_enter g with hk h2k hKlt holdLen hcapFit hflowFit hresFit hcapSpec hflowSpec holdRes
  obtain ⟨m, k, K_cap, cap, capLimbs, flow, flowLimbs, oldResFwd, oldLens⟩ := g
  dsimp only at hk h2k hKlt holdLen hcapFit hflowFit hresFit hcapSpec hflowSpec holdRes ⊢
  have hw1 : 1 < 2 ^ w := by
    have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  set resFwd : Fin m → List ℕ := fun e => subLimbs k (capLimbs e) (flowLimbs e)
  set fwdLens := List.ofFn fun e : Fin m => canonLen (resFwd e)
  set revLens := List.ofFn fun e : Fin m => canonLen (flowLimbs e)
  have hresSpec : ∀ e : Fin m, Limbs k (resFwd e) ∧ (resFwd e).length = K_cap ∧
      Nat.ofDigits (2 ^ k) (resFwd e) = cap e - flow e := fun e =>
    subLimbs_res_spec hk (hcapSpec e).1 (hflowSpec e).1 (hcapSpec e).2.1 (hflowSpec e).2.1
      (hcapSpec e).2.2 (hflowSpec e).2.2.1 (hflowSpec e).2.2.2
  have hfL_len : fwdLens.length = m := List.length_ofFn
  have hrL_len : revLens.length = m := List.length_ofFn
  sep_apply resCapCell_init (capL := capLimbs) (flowL := flowLimbs) (oldR := oldResFwd)
    (newR := resFwd) (fL := fwdLens) (rL := revLens) holdLen
  set oL1 := oldLens.take m
  set oL2 := oldLens.drop m
  iterate 3 sep_step
  sep_for (fun e (t : ℕ × ℕ × ℕ) =>
    ⟨[m, k, K_cap, pCapBuf, pFlow, pResFwdBuf, pResCapLens,
      pCapBuf + e * K_cap, pFlow + e * K_cap, pResFwdBuf + e * K_cap,
      e, t.1, t.2.1, t.2.2],
      e ≤ m, (320 * K_cap + 215) * (m - e) + 5,
      [∏ i ∈ Finset.range m, resCapCell m K_cap pCapBuf pFlow pResFwdBuf pResCapLens
        capLimbs flowLimbs oldResFwd resFwd oL1 oL2 fwdLens revLens e i]⟩)
    with ⟨tb, tl1, tl2⟩
  · have hmem : e ∈ Finset.range m := Finset.mem_range.mpr hhi
    have hc_e := hcapSpec ⟨e, hhi⟩
    have hc1 := hc_e.1
    have hf_e := hflowSpec ⟨e, hhi⟩
    have hf1 := hf_e.1
    have hr_e := hresSpec ⟨e, hhi⟩
    have hor_e := holdRes ⟨e, hhi⟩
    have hnext_c : pCapBuf + e * K_cap + K_cap = pCapBuf + (e + 1) * K_cap := by
      rw [Nat.succ_mul]; omega
    have hnext_f : pFlow + e * K_cap + K_cap = pFlow + (e + 1) * K_cap := by
      rw [Nat.succ_mul]; omega
    have hnext_r : pResFwdBuf + e * K_cap + K_cap = pResFwdBuf + (e + 1) * K_cap := by
      rw [Nat.succ_mul]; omega
    have hmul_le : (e + 1) * K_cap ≤ m * K_cap := Nat.mul_le_mul_right K_cap (by omega)
    have hTsub_le : Tsub (capLimbs ⟨e, hhi⟩).length ≤ 200 * K_cap + 100 := by
      rw [hc_e.2.1]; exact hsub_mono K_cap
    have hmul_sub_z : (320 * (K_cap : ℤ) + 215) * ((m : ℤ) - (e : ℤ)) =
        (320 * (K_cap : ℤ) + 215) + (320 * (K_cap : ℤ) + 215) * ((m : ℤ) - ((e + 1 : ℕ) : ℤ)) := by
      push_cast; ring
    sep_apply Assn.prod_eq_mul_erase hmem
      (resCapCell m K_cap pCapBuf pFlow pResFwdBuf pResCapLens
        capLimbs flowLimbs oldResFwd resFwd oL1 oL2 fwdLens revLens e)
    have hpop : resCapCell m K_cap pCapBuf pFlow pResFwdBuf pResCapLens
          capLimbs flowLimbs oldResFwd resFwd oL1 oL2 fwdLens revLens e e =
        Assn.list (pCapBuf + e * K_cap) (capLimbs ⟨e, hhi⟩) *
        Assn.list (pFlow + e * K_cap) (flowLimbs ⟨e, hhi⟩) *
        Assn.list (pResFwdBuf + e * K_cap) (oldResFwd ⟨e, hhi⟩) *
        Assn.list (pResCapLens + e) [oL1.getD e 0] *
        Assn.list (pResCapLens + m + e) [oL2.getD e 0] := by
      simp [resCapCell, hhi]
    sep_apply hpop
    sep_step from (k, capLimbs ⟨e, hhi⟩, flowLimbs ⟨e, hhi⟩, oldResFwd ⟨e, hhi⟩)
    sep_step from (resFwd ⟨e, hhi⟩)
    sep_step
    sep_step from (flowLimbs ⟨e, hhi⟩)
    sep_step
    have hfl_e : fwdLens.getD e 0 = canonLen (resFwd ⟨e, hhi⟩) := by
      rw [List.getD_eq_getElem _ _ (by simp [fwdLens]; omega)]; exact List.getElem_ofFn ..
    have hrl_e : revLens.getD e 0 = canonLen (flowLimbs ⟨e, hhi⟩) := by
      rw [List.getD_eq_getElem _ _ (by simp [revLens]; omega)]; exact List.getElem_ofFn ..
    subst hl1 hl2
    simp only [List.set_cons_zero]
    rw [← hfl_e, ← hrl_e]
    sep_apply resCapCell_step (pCapBuf := pCapBuf) (pFlow := pFlow)
      (pResFwdBuf := pResFwdBuf) (pResCapLens := pResCapLens)
      (capL := capLimbs) (flowL := flowLimbs) (oldR := oldResFwd) (newR := resFwd)
      (oL1 := oL1) (oL2 := oL2) (fL := fwdLens) (rL := revLens) hhi
    sep_run
  · sep_apply resCapCell_final (pCapBuf := pCapBuf) (pFlow := pFlow)
      (pResFwdBuf := pResFwdBuf) (pResCapLens := pResCapLens)
      (capL := capLimbs) (flowL := flowLimbs) (oldR := oldResFwd) (newR := resFwd)
      (oL1 := oL1) (oL2 := oL2) hfL_len hrL_len
    sep_run

/-! ### 3. Splitting/gluing canonical prefixes across `bitScale` -/

/-- Canonical residual capacity limb lists (`2 * m` entries) produced by `stage1ResCaps`:
forward residual capacities `resFwd[e].take (canonLen (resFwd e))` followed by reverse residual
capacities `flowLimbs[e].take (canonLen (flowLimbs e))`. -/
def resCapCanonLimbs {m : ℕ} (resFwd flowLimbs : Fin m → List ℕ) : List (List ℕ) :=
  (List.ofFn fun e : Fin m => (resFwd e).take (canonLen (resFwd e))) ++
  (List.ofFn fun e : Fin m => (flowLimbs e).take (canonLen (flowLimbs e)))

theorem resCapCanonLimbs_length {m : ℕ} (resFwd flowLimbs : Fin m → List ℕ) :
    (resCapCanonLimbs resFwd flowLimbs).length = 2 * m := by
  unfold resCapCanonLimbs; simp; omega

theorem resCapCanonLimbs_map_length {m : ℕ} (resFwd flowLimbs : Fin m → List ℕ)
    (K_cap : ℕ)
    (_hr : ∀ e, (resFwd e).length = K_cap) (_hf : ∀ e, (flowLimbs e).length = K_cap) :
    (resCapCanonLimbs resFwd flowLimbs).map List.length =
      (List.ofFn fun e : Fin m => canonLen (resFwd e)) ++
      (List.ofFn fun e : Fin m => canonLen (flowLimbs e)) := by
  unfold resCapCanonLimbs
  rw [List.map_append, List.map_ofFn, List.map_ofFn]
  congr 1 <;> refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
  · simp [canonLen_le]
  · simp [canonLen_le]

/-- Split the `m` forward residual buffers and `m` flow buffers into the `2 * m` canonical
residual capacity limb arrays (at `fwdPtrs ++ revPtrs`) plus their zero-padded tails. -/
theorem stage1ResCaps_split_for_bitScale {m K_cap pResFwdBuf pFlow : ℕ}
    (resFwd flowLimbs : Fin m → List ℕ)
    (hr : ∀ e, (resFwd e).length = K_cap) (hf : ∀ e, (flowLimbs e).length = K_cap) :
    (∏ e ∈ Finset.range m, Assn.list (pResFwdBuf + e * K_cap)
      (if h : e < m then resFwd ⟨e, h⟩ else [])) *
    (∏ e ∈ Finset.range m, Assn.list (pFlow + e * K_cap)
      (if h : e < m then flowLimbs ⟨e, h⟩ else [])) =
    (∏ a ∈ Finset.range (2 * m),
      Assn.list
        (((List.ofFn fun e : Fin m => pResFwdBuf + e.val * K_cap) ++
          (List.ofFn fun e : Fin m => pFlow + e.val * K_cap)).getD a 0)
        ((resCapCanonLimbs resFwd flowLimbs).getD a [])) *
    (∏ e ∈ Finset.range m,
      Assn.list (pResFwdBuf + e * K_cap + (if h : e < m then canonLen (resFwd ⟨e, h⟩) else 0))
        (List.replicate (K_cap - if h : e < m then canonLen (resFwd ⟨e, h⟩) else 0) 0)) *
    (∏ e ∈ Finset.range m,
      Assn.list (pFlow + e * K_cap + (if h : e < m then canonLen (flowLimbs ⟨e, h⟩) else 0))
        (List.replicate (K_cap - if h : e < m then canonLen (flowLimbs ⟨e, h⟩) else 0) 0)) := by
  have hsplit_one : ∀ (base : ℕ) (xs : List ℕ), xs.length = K_cap →
      Assn.list base xs =
        Assn.list base (xs.take (canonLen xs)) *
        Assn.list (base + canonLen xs) (List.replicate (K_cap - canonLen xs) 0) := by
    intro base xs hxlen
    conv_lhs => rw [← List.take_append_drop (canonLen xs) xs, drop_canonLen_eq_replicate, hxlen]
    rw [Assn.list_append, List.length_take, hxlen, Nat.min_eq_left (by rw [← hxlen]; exact canonLen_le xs)]
  have hR : (∏ e ∈ Finset.range m, Assn.list (pResFwdBuf + e * K_cap)
      (if h : e < m then resFwd ⟨e, h⟩ else [])) =
      (∏ e ∈ Finset.range m, Assn.list (pResFwdBuf + e * K_cap)
        (if h : e < m then (resFwd ⟨e, h⟩).take (canonLen (resFwd ⟨e, h⟩)) else [])) *
      (∏ e ∈ Finset.range m,
        Assn.list (pResFwdBuf + e * K_cap + (if h : e < m then canonLen (resFwd ⟨e, h⟩) else 0))
          (List.replicate (K_cap - if h : e < m then canonLen (resFwd ⟨e, h⟩) else 0) 0)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e he => ?_
    have hem : e < m := Finset.mem_range.mp he
    simp only [hem, ↓reduceDIte]
    exact hsplit_one _ _ (hr ⟨e, hem⟩)
  have hF : (∏ e ∈ Finset.range m, Assn.list (pFlow + e * K_cap)
      (if h : e < m then flowLimbs ⟨e, h⟩ else [])) =
      (∏ e ∈ Finset.range m, Assn.list (pFlow + e * K_cap)
        (if h : e < m then (flowLimbs ⟨e, h⟩).take (canonLen (flowLimbs ⟨e, h⟩)) else [])) *
      (∏ e ∈ Finset.range m,
        Assn.list (pFlow + e * K_cap + (if h : e < m then canonLen (flowLimbs ⟨e, h⟩) else 0))
          (List.replicate (K_cap - if h : e < m then canonLen (flowLimbs ⟨e, h⟩) else 0) 0)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e he => ?_
    have hem : e < m := Finset.mem_range.mp he
    simp only [hem, ↓reduceDIte]
    exact hsplit_one _ _ (hf ⟨e, hem⟩)
  have hprod2m :
      (∏ a ∈ Finset.range (2 * m),
        Assn.list
          (((List.ofFn fun e : Fin m => pResFwdBuf + e.val * K_cap) ++
            (List.ofFn fun e : Fin m => pFlow + e.val * K_cap)).getD a 0)
          ((resCapCanonLimbs resFwd flowLimbs).getD a [])) =
      (∏ e ∈ Finset.range m, Assn.list (pResFwdBuf + e * K_cap)
        (if h : e < m then (resFwd ⟨e, h⟩).take (canonLen (resFwd ⟨e, h⟩)) else [])) *
      (∏ e ∈ Finset.range m, Assn.list (pFlow + e * K_cap)
        (if h : e < m then (flowLimbs ⟨e, h⟩).take (canonLen (flowLimbs ⟨e, h⟩)) else [])) := by
    have hsplit2 : ∀ (f : ℕ → Assn), (∏ a ∈ Finset.range (m + m), f a) =
        (∏ e ∈ Finset.range m, f e) * (∏ e ∈ Finset.range m, f (m + e)) := by
      intro f
      induction m with
      | zero => simp
      | succ k _ =>
        have hstep : ∀ a b : ℕ, (∏ i ∈ Finset.range (a + b), f i) =
            (∏ i ∈ Finset.range a, f i) * (∏ i ∈ Finset.range b, f (a + i)) := by
          intro a b
          induction b with
          | zero => simp
          | succ b ih =>
            rw [← Nat.add_assoc, Finset.prod_range_succ, Finset.prod_range_succ, ih, mul_assoc]
        exact hstep (k + 1) (k + 1)
    rw [show 2 * m = m + m by omega, hsplit2]
    congr 1
    · refine Finset.prod_congr rfl fun e he => ?_
      have hem : e < m := Finset.mem_range.mp he
      simp only [hem, ↓reduceDIte, resCapCanonLimbs]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_ofFn,
        List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_ofFn]
    · refine Finset.prod_congr rfl fun e he => ?_
      have hem : e < m := Finset.mem_range.mp he
      have hptr_e :
          ((List.ofFn fun i : Fin m => pResFwdBuf + i.val * K_cap) ++
            (List.ofFn fun i : Fin m => pFlow + i.val * K_cap)).getD (m + e) 0 =
          pFlow + e * K_cap := by
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp)]
        simp
      have hlimb_e :
          (resCapCanonLimbs resFwd flowLimbs).getD (m + e) [] =
          (flowLimbs ⟨e, hem⟩).take (canonLen (flowLimbs ⟨e, hem⟩)) := by
        unfold resCapCanonLimbs
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp)]
        simp
      simp only [hem, ↓reduceDIte, hptr_e, hlimb_e]
  rw [hR, hF, hprod2m]
  simp only [mul_assoc, mul_left_comm]

end MinCostFlow.NarrowProg.Stage1
