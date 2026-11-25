module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Array
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1StartHelpers
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Dual-extraction graph writers and routing builder (Part 4a helpers)

This file provides the three `O(m + n + 1)` linear-scan helper procedures for Stage 1 dual
extraction (`Stage1Dual.lean`):
- `stage1WriteS`: writes `S.solverWords` for `S = (flagResidualGraph J fwd rev).shortestRoutingGraph`
  directly from `(pResTail, pResHead, pResCSign, pResCMag, pRho, pGCap)`.
- `stage1WriteQ`: writes `Qpos.solverWords` for `Qpos = extractDualFromFlagsCall J fwd rev`.
- `stage1BuildRouting`: computes `routing : Fin S.m → ℤ` from the bounded solver's output
  `d_dual : Fin Qpos.m → ℤ` and the presence arrays `(pRho, pGCap)`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Scaling.Machine
  MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate

/-! ### Helper: folding a product of 5-word edge records into `J.solverWords` -/

theorem prod_solverEdgeWords_eq_list (J : Circulation) (base : ℕ) :
    Assn.list base [J.n, J.m] *
      (∏ e ∈ Finset.range J.m, Assn.list (base + 2 + e * 5)
        (if h : e < J.m then J.solverEdgeWords ⟨e, h⟩ else [])) =
    Assn.list base J.solverWords := by
  have hflat : ∀ (k : ℕ) (hk : k ≤ J.m),
      (∏ e ∈ Finset.range k, Assn.list (base + 2 + e * 5)
        (if h : e < J.m then J.solverEdgeWords ⟨e, h⟩ else [])) =
      Assn.list (base + 2) (((List.finRange J.m).take k).flatMap J.solverEdgeWords) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Finset.prod_range_succ, ih (by omega)]
      have htake : (List.finRange J.m).take (k + 1) =
          (List.finRange J.m).take k ++ [⟨k, by omega⟩] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega), Option.toList_some]
        simp
      rw [htake, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        Assn.list_append]
      have hlen : (((List.finRange J.m).take k).flatMap J.solverEdgeWords).length = k * 5 := by
        rw [Circulation.solverEdgeRecords_length, List.length_take, List.length_finRange,
          Nat.min_eq_left (by omega)]
        omega
      rw [hlen]
      simp only [show k < J.m by omega, ↓reduceDIte]
  have hfull := hflat J.m le_rfl
  rw [List.take_of_length_le (by simp)] at hfull
  rw [hfull, show base + 2 = base + [J.n, J.m].length from rfl, ← Assn.list_append]
  rfl

private theorem prod_split_three {n1 n2 n3 : ℕ} (f : ℕ → Assn) :
    (∏ i ∈ Finset.range (n1 + n2 + n3), f i) =
      (∏ i ∈ Finset.range n1, f i) *
      (∏ i ∈ Finset.range n2, f (n1 + i)) *
      (∏ i ∈ Finset.range n3, f (n1 + n2 + i)) := by
  have h2 : ∀ a b : ℕ, (∏ i ∈ Finset.range (a + b), f i) =
      (∏ i ∈ Finset.range a, f i) * (∏ i ∈ Finset.range b, f (a + i)) := by
    intro a b
    induction b with
    | zero => simp
    | succ b ih =>
      rw [← Nat.add_assoc, Finset.prod_range_succ, Finset.prod_range_succ, ih, mul_assoc]
  rw [h2 (n1 + n2) n3, h2 n1 n2]

private theorem free_split_solverWords {w a n1 n2 n3 : ℕ}
    (hfit : a + 2 + (n1 + n2 + n3) * 5 ≤ 2 ^ w) :
    Assn.free a (2 + (n1 + n2 + n3) * 5) =
      Assn.list a (List.replicate 2 0) *
      (∏ i ∈ Finset.range n1, Assn.list (a + 2 + i * 5) (List.replicate 5 0)) *
      (∏ i ∈ Finset.range n2, Assn.list (a + 2 + (n1 + i) * 5) (List.replicate 5 0)) *
      (∏ i ∈ Finset.range n3, Assn.list (a + 2 + (n1 + n2 + i) * 5) (List.replicate 5 0)) := by
  have _ := hfit
  rw [Assn.free_add', show Assn.free a 2 = Assn.list a (List.replicate 2 0) from rfl,
    free_mul_eq_prod, prod_split_three]
  simp only [mul_assoc]

/-! ### 1. Writing `S.solverWords` (`stage1WriteS`) -/

/-- Write `S.solverWords` at `pS` for `S = (flagResidualGraph J fwd rev).shortestRoutingGraph`,
where `fwd a = decide (0 < rho[a])` and `rev a = decide (0 < gCap[a])`. -/
wram_def stage1WriteS (n', mJ, pResTail, pResHead, pResCSign, pResCMag, pRho, pGCap, pS) {
  mem[pS] := n' + 1
  mem[pS + 1] := 2 * mJ + n'
  cur := pS + 2
  for a in 0 .. mJ {
    t := mem[pResTail + a]
    h := mem[pResHead + a]
    r := mem[pRho + a]
    cap := 0
    if 0 < r {
      cap := n' + 1
    }
    cs := mem[pResCSign + a]
    cm := mem[pResCMag + a]
    mem[cur] := t
    mem[cur + 1] := h
    mem[cur + 2] := cap
    mem[cur + 3] := cs
    mem[cur + 4] := cm
    cur := cur + 5
  }
  for a in 0 .. mJ {
    t := mem[pResTail + a]
    h := mem[pResHead + a]
    r := mem[pGCap + a]
    cap := 0
    if 0 < r {
      cap := n' + 1
    }
    cs := mem[pResCSign + a]
    cm := mem[pResCMag + a]
    ns := 0
    if 0 < cm {
      ns := 1 - cs
    }
    mem[cur] := h
    mem[cur + 1] := t
    mem[cur + 2] := cap
    mem[cur + 3] := ns
    mem[cur + 4] := cm
    cur := cur + 5
  }
  for a in 0 .. n' {
    mem[cur] := n'
    mem[cur + 1] := a
    mem[cur + 2] := n' + 1
    mem[cur + 3] := 0
    mem[cur + 4] := 0
    cur := cur + 5
  }
  return 0
}

/-- Ghost input bundle shared by `stage1WriteS` and `stage1WriteQ`. -/
structure Stage1DualGraphIn where
  J : Circulation
  rho : List ℕ
  gCap : List ℕ

/-- Active-flag functions read from `rho` and `gCap`. -/
def dualFwdFlags (J : Circulation) (rho : List ℕ) : Fin J.m → Bool :=
  fun a => decide (0 < rho.getD a.val 0)

def dualRevFlags (J : Circulation) (gCap : List ℕ) : Fin J.m → Bool :=
  fun a => decide (0 < gCap.getD a.val 0)

/-- Specification of `stage1WriteS`. -/
def stage1WriteSSpec (w : ℕ) : Spec Stage1DualGraphIn where
  pre := fun g args =>
    ⨆ (pT : ℕ) (pH : ℕ) (pCS : ℕ) (pCM : ℕ) (pRho : ℕ) (pGCap : ℕ) (pS : ℕ),
      let S := (flagResidualGraph g.J (dualFwdFlags g.J g.rho) (dualRevFlags g.J g.gCap)).shortestRoutingGraph
      ⌜args = [g.J.n, g.J.m, pT, pH, pCS, pCM, pRho, pGCap, pS] ∧
        g.rho.length = g.J.m ∧ g.gCap.length = g.J.m ∧
        pS + S.solverWords.length < 2 ^ w ∧
        2 * g.J.m + g.J.n < 2 ^ w ∧ g.J.n + 1 < 2 ^ w ∧ 5 < 2 ^ w⌝ *
      Assn.list pT (List.ofFn fun a : Fin g.J.m => (g.J.tail a).val) *
      Assn.list pH (List.ofFn fun a : Fin g.J.m => (g.J.head a).val) *
      Assn.list pCS (List.ofFn fun a : Fin g.J.m => if g.J.cost a < 0 then 1 else 0) *
      Assn.list pCM (List.ofFn fun a : Fin g.J.m => (g.J.cost a).natAbs) *
      Assn.list pRho g.rho *
      Assn.list pGCap g.gCap *
      Assn.free pS S.solverWords.length
  post := fun g args v =>
    ⨆ (pT : ℕ) (pH : ℕ) (pCS : ℕ) (pCM : ℕ) (pRho : ℕ) (pGCap : ℕ) (pS : ℕ),
      let S := (flagResidualGraph g.J (dualFwdFlags g.J g.rho) (dualRevFlags g.J g.gCap)).shortestRoutingGraph
      ⌜args = [g.J.n, g.J.m, pT, pH, pCS, pCM, pRho, pGCap, pS] ∧ v = 0⌝ *
      Assn.list pT (List.ofFn fun a : Fin g.J.m => (g.J.tail a).val) *
      Assn.list pH (List.ofFn fun a : Fin g.J.m => (g.J.head a).val) *
      Assn.list pCS (List.ofFn fun a : Fin g.J.m => if g.J.cost a < 0 then 1 else 0) *
      Assn.list pCM (List.ofFn fun a : Fin g.J.m => (g.J.cost a).natAbs) *
      Assn.list pRho g.rho *
      Assn.list pGCap g.gCap *
      Assn.list pS S.solverWords

private theorem negCost_sign (c : ℤ) :
    (if -c < 0 then 1 else 0) = if 0 < c.natAbs then 1 - (if c < 0 then 1 else 0) else 0 := by
  split_ifs <;> omega

private theorem S_edge_fwd (J : Circulation) (fwd rev : Fin J.m → Bool) (a : Fin J.m) :
    let S := (flagResidualGraph J fwd rev).shortestRoutingGraph
    S.solverEdgeWords ⟨a.val, by change a.val < (J.m + J.m) + J.n; omega⟩ =
      [(J.tail a).val, (J.head a).val, if fwd a then J.n + 1 else 0,
       if J.cost a < 0 then 1 else 0, (J.cost a).natAbs] := by
  dsimp only [Circulation.solverEdgeWords, Circulation.shortestRoutingGraph, flagResidualGraph]
  have h1 : (⟨a.val, by omega⟩ : Fin ((J.m + J.m) + J.n)) =
      Fin.castAdd J.n (Fin.castAdd J.m a) := by ext; rfl
  rw [h1]
  simp only [Fin.addCases_left, Fin.val_castSucc]
  cases fwd a <;> simp

private theorem S_edge_rev (J : Circulation) (fwd rev : Fin J.m → Bool) (a : Fin J.m) :
    let S := (flagResidualGraph J fwd rev).shortestRoutingGraph
    S.solverEdgeWords ⟨J.m + a.val, by change J.m + a.val < (J.m + J.m) + J.n; omega⟩ =
      [(J.head a).val, (J.tail a).val, if rev a then J.n + 1 else 0,
       if -J.cost a < 0 then 1 else 0, (J.cost a).natAbs] := by
  dsimp only [Circulation.solverEdgeWords, Circulation.shortestRoutingGraph, flagResidualGraph]
  have h1 : (⟨J.m + a.val, by omega⟩ : Fin ((J.m + J.m) + J.n)) =
      Fin.castAdd J.n (Fin.natAdd J.m a) := by ext; simp [Fin.natAdd]
  rw [h1]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castSucc, Int.natAbs_neg]
  cases rev a <;> simp

private theorem S_edge_src (J : Circulation) (fwd rev : Fin J.m → Bool) (v : Fin J.n) :
    let S := (flagResidualGraph J fwd rev).shortestRoutingGraph
    S.solverEdgeWords ⟨J.m + J.m + v.val, by change J.m + J.m + v.val < (J.m + J.m) + J.n; omega⟩ =
      [J.n, v.val, J.n + 1, 0, 0] := by
  dsimp only [Circulation.solverEdgeWords, Circulation.shortestRoutingGraph, flagResidualGraph]
  have h1 : (⟨J.m + J.m + v.val, by omega⟩ : Fin ((J.m + J.m) + J.n)) =
      Fin.natAdd (J.m + J.m) v := by ext; simp [Fin.natAdd]
  rw [h1]
  simp only [Fin.addCases_right, Fin.val_last, Fin.val_castSucc, lt_irrefl, ↓reduceIte, Int.natAbs_zero]

theorem stage1WriteS_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1WriteS) :
    Meets w p f ((stage1WriteSSpec w).withCost fun g _ => 210 * g.J.m + 70 * g.J.n + 100) := by
  sep_enter g with hrho hgcap hpS_fit hSm_lt hn1 hw5
  obtain ⟨J, rho, gCap⟩ := g
  dsimp only at hrho hgcap hpS_fit hSm_lt hn1 hw5 ⊢
  set fwd := dualFwdFlags J rho
  set rev := dualRevFlags J gCap
  set S := (flagResidualGraph J fwd rev).shortestRoutingGraph with hS_def
  have hSlen : S.solverWords.length = 2 + (J.m + J.m + J.n) * 5 := by
    rw [S.solverWords_length]; change 2 + 5 * ((J.m + J.m) + J.n) = _; omega
  rw [hSlen] at hpS_fit ⊢
  sep_apply free_split_solverWords (w := w) (n1 := J.m) (n2 := J.m) (n3 := J.n) (by omega)
  sep_step; sep_step; sep_step
  have hhdr_eq : ((List.replicate 2 0).set 0 (J.n + 1)).set 1 (2 * J.m + J.n) =
      [J.n + 1, 2 * J.m + J.n] := rfl
  rw [hhdr_eq]
  -- Loop 1: forward edges `0 .. J.m`
  sep_for (fun a (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
    ⟨[J.n, J.m, pT, pH, pCS, pCM, pRho, pGCap, pS, pS + 2 + a * 5, a,
      t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2, 0],
      a ≤ J.m, 85 * (J.m - a) + (110 * J.m + 65 * J.n + 50),
      [Assn.list pT (List.ofFn fun e : Fin J.m => (J.tail e).val),
       Assn.list pH (List.ofFn fun e : Fin J.m => (J.head e).val),
       Assn.list pCS (List.ofFn fun e : Fin J.m => if J.cost e < 0 then 1 else 0),
       Assn.list pCM (List.ofFn fun e : Fin J.m => (J.cost e).natAbs),
       Assn.list pRho rho,
       Assn.list pGCap gCap,
       Assn.list pS [J.n + 1, 2 * J.m + J.n],
       ∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + i * 5)
         (if i < a then (if h : i < J.m then S.solverEdgeWords ⟨i, by change i < (J.m + J.m) + J.n; omega⟩ else [])
          else List.replicate 5 0),
       ∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + (J.m + i) * 5) (List.replicate 5 0),
       ∏ i ∈ Finset.range J.n, Assn.list (pS + 2 + (J.m + J.m + i) * 5) (List.replicate 5 0)]⟩)
    with ⟨t0, t1, t2, t3, t4, t5⟩
  · have hmem : a ∈ Finset.range J.m := Finset.mem_range.mpr hhi
    have hcur_next : pS + 2 + a * 5 + 5 = pS + 2 + (a + 1) * 5 := by omega
    have hcur_lt : pS + 2 + (a + 1) * 5 < 2 ^ w := by omega
    have hr_a : rho[a]'(by omega) = rho.getD a 0 := (List.getD_eq_getElem _ _ (by omega)).symm
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun i => Assn.list (pS + 2 + i * 5)
        (if i < a then (if h : i < J.m then S.solverEdgeWords ⟨i, by change i < (J.m + J.m) + J.n; omega⟩ else [])
         else List.replicate 5 0))
    have hnotlt : (if a < a then (if h : a < J.m then S.solverEdgeWords ⟨a, by change a < (J.m + J.m) + J.n; omega⟩ else [])
        else List.replicate 5 0) = List.replicate 5 0 := by simp
    rw [hnotlt]
    have hse := S_edge_fwd J fwd rev ⟨a, hhi⟩
    have hupd : ∀ w_list : List ℕ, w_list = S.solverEdgeWords ⟨a, by change a < (J.m + J.m) + J.n; omega⟩ →
        Assn.list (pS + 2 + a * 5) w_list *
        (∏ i ∈ (Finset.range J.m).erase a, Assn.list (pS + 2 + i * 5)
          (if i < a then (if h : i < J.m then S.solverEdgeWords ⟨i, by change i < (J.m + J.m) + J.n; omega⟩ else [])
           else List.replicate 5 0)) =
        ∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + i * 5)
          (if i < a + 1 then (if h : i < J.m then S.solverEdgeWords ⟨i, by change i < (J.m + J.m) + J.n; omega⟩ else [])
           else List.replicate 5 0) := by
      intro w_list hw_eq; rw [hw_eq, Assn.prod_eq_mul_erase hmem]
      simp only [Nat.lt_succ_self, ↓reduceIte, hhi, ↓reduceDIte]
      congr 1; refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ a := (Finset.mem_erase.mp hi).1
      simp only [show (i < a) ↔ (i < a + 1) by omega]
    have ht_a : (List.ofFn fun e : Fin J.m => (J.tail e).val)[a]'(by simp; omega) =
        (J.tail ⟨a, hhi⟩).val := List.getElem_ofFn ..
    have hh_a : (List.ofFn fun e : Fin J.m => (J.head e).val)[a]'(by simp; omega) =
        (J.head ⟨a, hhi⟩).val := List.getElem_ofFn ..
    have hcs_a : (List.ofFn fun e : Fin J.m => if J.cost e < 0 then 1 else 0)[a]'(by simp; omega) =
        if J.cost ⟨a, hhi⟩ < 0 then 1 else 0 := List.getElem_ofFn ..
    have hcm_a : (List.ofFn fun e : Fin J.m => (J.cost e).natAbs)[a]'(by simp; omega) =
        (J.cost ⟨a, hhi⟩).natAbs := List.getElem_ofFn ..
    by_cases hpos : 0 < rho.getD a 0
    · have hfwd_t : fwd ⟨a, hhi⟩ = true := by simp [fwd, dualFwdFlags]; exact hpos
      sep_step; rw [ht_a] at ht; subst ht
      sep_step; rw [hh_a] at hh; subst hh
      sep_step; sep_step
      sep_step
      · sep_step
        sep_step; rw [hcs_a] at hcs; subst hcs
        sep_step; rw [hcm_a] at hcm; subst hcm
        iterate 5 sep_step
        sep_apply hupd _ (by rw [hse, hfwd_t]; simp [hcap])
        sep_run
    · have hfwd_f : fwd ⟨a, hhi⟩ = false := by unfold fwd dualFwdFlags; exact decide_eq_false hpos
      sep_step; rw [ht_a] at ht; subst ht
      sep_step; rw [hh_a] at hh; subst hh
      sep_step; sep_step
      sep_step
      · sep_step
        sep_step; rw [hcs_a] at hcs; subst hcs
        sep_step; rw [hcm_a] at hcm; subst hcm
        iterate 5 sep_step
        sep_apply hupd _ (by rw [hse, hfwd_f]; simp)
        sep_run
  -- After Loop 1: Loop 2 (reverse edges `0 .. J.m`)
  have hL1_end :
      (∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + i * 5)
        (if i < J.m then (if h : i < J.m then S.solverEdgeWords ⟨i, by change i < (J.m + J.m) + J.n; omega⟩ else [])
         else List.replicate 5 0)) =
      ∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + i * 5)
        (if h : i < S.m then S.solverEdgeWords ⟨i, h⟩ else []) :=
    Finset.prod_congr rfl fun i hi => by
      have hlt := Finset.mem_range.mp hi
      simp [hlt, show i < S.m by change i < (J.m + J.m) + J.n; omega]
  rw [hL1_end]
  sep_for (fun a (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
    ⟨[J.n, J.m, pT, pH, pCS, pCM, pRho, pGCap, pS, pS + 2 + (J.m + a) * 5, a,
      t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2],
      a ≤ J.m, 95 * (J.m - a) + (65 * J.n + 30),
      [Assn.list pT (List.ofFn fun e : Fin J.m => (J.tail e).val),
       Assn.list pH (List.ofFn fun e : Fin J.m => (J.head e).val),
       Assn.list pCS (List.ofFn fun e : Fin J.m => if J.cost e < 0 then 1 else 0),
       Assn.list pCM (List.ofFn fun e : Fin J.m => (J.cost e).natAbs),
       Assn.list pRho rho,
       Assn.list pGCap gCap,
       Assn.list pS [J.n + 1, 2 * J.m + J.n],
       ∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + i * 5)
         (if h : i < S.m then S.solverEdgeWords ⟨i, h⟩ else []),
       ∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + (J.m + i) * 5)
         (if i < a then (if h : J.m + i < S.m then S.solverEdgeWords ⟨J.m + i, h⟩ else [])
          else List.replicate 5 0),
       ∏ i ∈ Finset.range J.n, Assn.list (pS + 2 + (J.m + J.m + i) * 5) (List.replicate 5 0)]⟩)
    with ⟨t0, t1, t2, t3, t4, t5, t6⟩
  · have hmem : a ∈ Finset.range J.m := Finset.mem_range.mpr hhi
    have hcur_next : pS + 2 + (J.m + a) * 5 + 5 = pS + 2 + (J.m + (a + 1)) * 5 := by omega
    have hcur_lt : pS + 2 + (J.m + (a + 1)) * 5 < 2 ^ w := by omega
    have hg_a : gCap[a]'(by omega) = gCap.getD a 0 := (List.getD_eq_getElem _ _ (by omega)).symm
    have hcm_a : (List.ofFn fun e : Fin J.m => (J.cost e).natAbs)[a]'(by simp; omega) =
        (J.cost ⟨a, hhi⟩).natAbs := List.getElem_ofFn ..
    have hcs_a : (List.ofFn fun e : Fin J.m => if J.cost e < 0 then 1 else 0)[a]'(by simp; omega) =
        if J.cost ⟨a, hhi⟩ < 0 then 1 else 0 := List.getElem_ofFn ..
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun i => Assn.list (pS + 2 + (J.m + i) * 5)
        (if i < a then (if h : J.m + i < S.m then S.solverEdgeWords ⟨J.m + i, h⟩ else [])
         else List.replicate 5 0))
    have hnotlt : (if a < a then (if h : J.m + a < S.m then S.solverEdgeWords ⟨J.m + a, h⟩ else [])
        else List.replicate 5 0) = List.replicate 5 0 := by simp
    rw [hnotlt]
    have hse := S_edge_rev J fwd rev ⟨a, hhi⟩
    have hns := negCost_sign (J.cost ⟨a, hhi⟩)
    have hupd : ∀ w_list : List ℕ, w_list = S.solverEdgeWords ⟨J.m + a, by change J.m + a < (J.m + J.m) + J.n; omega⟩ →
        Assn.list (pS + 2 + (J.m + a) * 5) w_list *
        (∏ i ∈ (Finset.range J.m).erase a, Assn.list (pS + 2 + (J.m + i) * 5)
          (if i < a then (if h : J.m + i < S.m then S.solverEdgeWords ⟨J.m + i, h⟩ else [])
           else List.replicate 5 0)) =
        ∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + (J.m + i) * 5)
          (if i < a + 1 then (if h : J.m + i < S.m then S.solverEdgeWords ⟨J.m + i, h⟩ else [])
           else List.replicate 5 0) := by
      intro w_list hw_eq; rw [hw_eq, Assn.prod_eq_mul_erase hmem]
      simp only [Nat.lt_succ_self, ↓reduceIte, show J.m + a < S.m by change J.m + a < (J.m + J.m) + J.n; omega, ↓reduceDIte]
      congr 1; refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ a := (Finset.mem_erase.mp hi).1
      simp only [show (i < a) ↔ (i < a + 1) by omega]
    have ht_a : (List.ofFn fun e : Fin J.m => (J.tail e).val)[a]'(by simp; omega) =
        (J.tail ⟨a, hhi⟩).val := List.getElem_ofFn ..
    have hh_a : (List.ofFn fun e : Fin J.m => (J.head e).val)[a]'(by simp; omega) =
        (J.head ⟨a, hhi⟩).val := List.getElem_ofFn ..
    -- Step through loads and both tiny conditionals
    sep_step; rw [ht_a] at ht; subst ht
    sep_step; rw [hh_a] at hh; subst hh
    sep_step; sep_step
    by_cases hpos : 0 < gCap.getD a 0
    · have hrev_t : rev ⟨a, hhi⟩ = true := by simp [rev, dualRevFlags]; exact hpos
      sep_step
      · sep_step; sep_step; sep_step; sep_step
        rw [hcm_a] at hcm; subst hcm
        rw [hcs_a] at hcs; subst hcs
        by_cases hcm0 : 0 < (J.cost ⟨a, hhi⟩).natAbs
        · sep_step
          · iterate 6 sep_step
            sep_apply hupd _ (by rw [hse, hrev_t, hns]; simp [hcm0, hcap, hns_1])
            sep_run
        · sep_step
          · have hcm_eq : (J.cost ⟨a, hhi⟩).natAbs = 0 := by omega
            iterate 6 sep_step
            sep_apply hupd _ (by rw [hse, hrev_t, hns]; simp [hcm_eq, hcap])
            sep_run
    · have hrev_f : rev ⟨a, hhi⟩ = false := by unfold rev dualRevFlags; exact decide_eq_false hpos
      sep_step
      · sep_step; sep_step; sep_step; sep_step
        rw [hcm_a] at hcm; subst hcm
        rw [hcs_a] at hcs; subst hcs
        by_cases hcm0 : 0 < (J.cost ⟨a, hhi⟩).natAbs
        · sep_step
          · iterate 6 sep_step
            sep_apply hupd _ (by rw [hse, hrev_f, hns]; simp [hcm0, hns_1])
            sep_run
        · sep_step
          · have hcm_eq : (J.cost ⟨a, hhi⟩).natAbs = 0 := by omega
            iterate 6 sep_step
            sep_apply hupd _ (by rw [hse, hrev_f, hns]; simp [hcm_eq])
            sep_run
  -- After Loop 2: Loop 3 (super-source arcs `0 .. J.n`)
  have hL2_end :
      (∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + (J.m + i) * 5)
        (if i < J.m then (if h : J.m + i < S.m then S.solverEdgeWords ⟨J.m + i, h⟩ else [])
         else List.replicate 5 0)) =
      ∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + (J.m + i) * 5)
        (if h : J.m + i < S.m then S.solverEdgeWords ⟨J.m + i, h⟩ else []) :=
    Finset.prod_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
  rw [hL2_end]
  sep_for (fun a =>
    ⟨[J.n, J.m, pT, pH, pCS, pCM, pRho, pGCap, pS, pS + 2 + (J.m + J.m + a) * 5,
      a, t0, t1, t2, t3, t4, t5, t6],
      a ≤ J.n, 55 * (J.n - a) + 10,
      [Assn.list pT (List.ofFn fun e : Fin J.m => (J.tail e).val),
       Assn.list pH (List.ofFn fun e : Fin J.m => (J.head e).val),
       Assn.list pCS (List.ofFn fun e : Fin J.m => if J.cost e < 0 then 1 else 0),
       Assn.list pCM (List.ofFn fun e : Fin J.m => (J.cost e).natAbs),
       Assn.list pRho rho,
       Assn.list pGCap gCap,
       Assn.list pS [J.n + 1, 2 * J.m + J.n],
       ∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + i * 5)
         (if h : i < S.m then S.solverEdgeWords ⟨i, h⟩ else []),
       ∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + (J.m + i) * 5)
         (if h : J.m + i < S.m then S.solverEdgeWords ⟨J.m + i, h⟩ else []),
       ∏ i ∈ Finset.range J.n, Assn.list (pS + 2 + (J.m + J.m + i) * 5)
         (if i < a then (if h : J.m + J.m + i < S.m then S.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])
          else List.replicate 5 0)]⟩)
  · have hmem : a ∈ Finset.range J.n := Finset.mem_range.mpr hhi
    have hcur_next : pS + 2 + (J.m + J.m + a) * 5 + 5 = pS + 2 + (J.m + J.m + (a + 1)) * 5 := by omega
    have hcur_lt : pS + 2 + (J.m + J.m + (a + 1)) * 5 < 2 ^ w := by omega
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun i => Assn.list (pS + 2 + (J.m + J.m + i) * 5)
        (if i < a then (if h : J.m + J.m + i < S.m then S.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])
         else List.replicate 5 0))
    have hnotlt : (if a < a then (if h : J.m + J.m + a < S.m then S.solverEdgeWords ⟨J.m + J.m + a, h⟩ else [])
        else List.replicate 5 0) = List.replicate 5 0 := by simp
    rw [hnotlt]
    have hse := S_edge_src J fwd rev ⟨a, hhi⟩
    iterate 5 sep_step
    have hupd :
        Assn.list (pS + 2 + (J.m + J.m + a) * 5) [J.n, a, J.n + 1, 0, 0] *
        (∏ i ∈ (Finset.range J.n).erase a, Assn.list (pS + 2 + (J.m + J.m + i) * 5)
          (if i < a then (if h : J.m + J.m + i < S.m then S.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])
           else List.replicate 5 0)) =
        ∏ i ∈ Finset.range J.n, Assn.list (pS + 2 + (J.m + J.m + i) * 5)
          (if i < a + 1 then (if h : J.m + J.m + i < S.m then S.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])
           else List.replicate 5 0) := by
      rw [← hse, Assn.prod_eq_mul_erase hmem]
      simp only [Nat.lt_succ_self, ↓reduceIte, show J.m + J.m + a < S.m by change J.m + J.m + a < (J.m + J.m) + J.n; omega, ↓reduceDIte]
      congr 1; refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ a := (Finset.mem_erase.mp hi).1
      simp only [show (i < a) ↔ (i < a + 1) by omega]
    sep_apply hupd
    sep_run
  -- Merge all 3 products + header into `Assn.list pS S.solverWords`
  have hL3_end :
      (∏ i ∈ Finset.range J.n, Assn.list (pS + 2 + (J.m + J.m + i) * 5)
        (if i < J.n then (if h : J.m + J.m + i < S.m then S.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])
         else List.replicate 5 0)) =
      ∏ i ∈ Finset.range J.n, Assn.list (pS + 2 + (J.m + J.m + i) * 5)
        (if h : J.m + J.m + i < S.m then S.solverEdgeWords ⟨J.m + J.m + i, h⟩ else []) :=
    Finset.prod_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
  rw [hL3_end]
  have hmergeS :
      Assn.list pS [J.n + 1, 2 * J.m + J.n] *
      (∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + i * 5) (if h : i < S.m then S.solverEdgeWords ⟨i, h⟩ else [])) *
      (∏ i ∈ Finset.range J.m, Assn.list (pS + 2 + (J.m + i) * 5) (if h : J.m + i < S.m then S.solverEdgeWords ⟨J.m + i, h⟩ else [])) *
      (∏ i ∈ Finset.range J.n, Assn.list (pS + 2 + (J.m + J.m + i) * 5) (if h : J.m + J.m + i < S.m then S.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])) =
      Assn.list pS S.solverWords := by
    have hprod := (prod_split_three (n1 := J.m) (n2 := J.m) (n3 := J.n)
      (fun e => Assn.list (pS + 2 + e * 5) (if h : e < S.m then S.solverEdgeWords ⟨e, h⟩ else []))).symm
    have h2m : 2 * J.m + J.n = S.m := by change 2 * J.m + J.n = (J.m + J.m) + J.n; omega
    have hSn : J.n + 1 = S.n := rfl
    rw [hSn, h2m, mul_assoc, mul_assoc, ← mul_assoc (∏ i ∈ Finset.range J.m, _), hprod]
    exact prod_solverEdgeWords_eq_list S pS
  sep_apply hmergeS
  sep_run

end MinCostFlow.NarrowProg.Stage1
