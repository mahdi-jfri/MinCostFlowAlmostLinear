module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Array
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1StartHelpers
public import MinCostFlow.NarrowProg.Stage1DualWrite
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Dual-extraction solver-graph writer (`stage1WriteQEdges`, `stage1WriteQ`)

Writes `Qpos.solverWords` for `Qpos = extractDualFromFlagsCall J fwd rev` directly from
`(pResTail, pResHead, pResCSign, pResCMag, pRho, pGCap)` in `O(J.m + J.n + 1)` steps.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Scaling.Machine
  MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate

private theorem prod_split_two {n1 n2 : ℕ} (f : ℕ → Assn) :
    (∏ i ∈ Finset.range (n1 + n2), f i) =
      (∏ i ∈ Finset.range n1, f i) * (∏ i ∈ Finset.range n2, f (n1 + i)) := by
  induction n2 with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, Finset.prod_range_succ, Finset.prod_range_succ, ih, mul_assoc]

private theorem prod_split_five {n1 n2 n3 n4 n5 : ℕ} (f : ℕ → Assn) :
    (∏ i ∈ Finset.range (n1 + n2 + n3 + n4 + n5), f i) =
      (∏ i ∈ Finset.range n1, f i) *
      (∏ i ∈ Finset.range n2, f (n1 + i)) *
      (∏ i ∈ Finset.range n3, f (n1 + n2 + i)) *
      (∏ i ∈ Finset.range n4, f (n1 + n2 + n3 + i)) *
      (∏ i ∈ Finset.range n5, f (n1 + n2 + n3 + n4 + i)) := by
  rw [prod_split_two (n1 := n1 + n2 + n3 + n4) (n2 := n5),
    prod_split_two (n1 := n1 + n2 + n3) (n2 := n4),
    prod_split_two (n1 := n1 + n2) (n2 := n3), prod_split_two (n1 := n1) (n2 := n2)]

private theorem free_split_solverWords5 {a n1 n2 n3 n4 n5 : ℕ} :
    Assn.free a (2 + (n1 + n2 + n3 + n4 + n5) * 5) =
      Assn.list a (List.replicate 2 0) *
      (∏ i ∈ Finset.range n1, Assn.list (a + 2 + i * 5) (List.replicate 5 0)) *
      (∏ i ∈ Finset.range n2, Assn.list (a + 2 + (n1 + i) * 5) (List.replicate 5 0)) *
      (∏ i ∈ Finset.range n3, Assn.list (a + 2 + (n1 + n2 + i) * 5) (List.replicate 5 0)) *
      (∏ i ∈ Finset.range n4, Assn.list (a + 2 + (n1 + n2 + n3 + i) * 5) (List.replicate 5 0)) *
      (∏ i ∈ Finset.range n5, Assn.list (a + 2 + (n1 + n2 + n3 + n4 + i) * 5) (List.replicate 5 0)) := by
  rw [Assn.free_add', show Assn.free a 2 = Assn.list a (List.replicate 2 0) from rfl,
    free_mul_eq_prod, prod_split_five]
  simp only [mul_assoc]

/-! ### 1. Writing the active-edge halves (`stage1WriteQEdges`) -/

/-- Write the two active-edge halves (`0 .. mJ` forward and `0 .. mJ` reverse) of `Qpos`
starting at `pQ + 2`. -/
wram_def stage1WriteQEdges (n', mJ, pResTail, pResHead, pResCSign, pResCMag, pRho, pGCap, pQ) {
  cur := pQ + 2
  for a in 0 .. mJ {
    r := mem[pRho + a]
    if 0 < r {
      t := mem[pResTail + a]
      h := mem[pResHead + a]
      cs := mem[pResCSign + a]
      cm := mem[pResCMag + a]
      mem[cur] := t
      mem[cur + 1] := h
      mem[cur + 2] := n' + 1
      mem[cur + 3] := cs
      mem[cur + 4] := cm
      cur := cur + 5
    } else {
      mem[cur] := n' + 1
      mem[cur + 1] := n' + 1
      mem[cur + 2] := 1
      mem[cur + 3] := 0
      mem[cur + 4] := 0
      cur := cur + 5
    }
  }
  for a in 0 .. mJ {
    r := mem[pGCap + a]
    if 0 < r {
      t := mem[pResTail + a]
      h := mem[pResHead + a]
      cs := mem[pResCSign + a]
      cm := mem[pResCMag + a]
      ns := 0
      if 0 < cm {
        ns := 1 - cs
      }
      mem[cur] := h
      mem[cur + 1] := t
      mem[cur + 2] := n' + 1
      mem[cur + 3] := ns
      mem[cur + 4] := cm
      cur := cur + 5
    } else {
      mem[cur] := n' + 1
      mem[cur + 1] := n' + 1
      mem[cur + 2] := 1
      mem[cur + 3] := 0
      mem[cur + 4] := 0
      cur := cur + 5
    }
  }
  return cur
}

/-- Write the header `[n' + 2, 4 * mJ + 2 * n']`, the two active-edge halves via `edgesIdx`,
and the three remaining blocks (forward super-source `0 .. n'`, reverse dummy loops `0 .. 2 * mJ`,
and reverse super-source `0 .. n'`) of `Qpos.solverWords` at `pQ`. -/
wram_def stage1WriteQ (edgesIdx : ℕ)
    (n', mJ, pResTail, pResHead, pResCSign, pResCMag, pRho, pGCap, pQ) {
  mem[pQ] := n' + 2
  mem[pQ + 1] := 4 * mJ + 2 * n'
  cur := edgesIdx(n', mJ, pResTail, pResHead, pResCSign, pResCMag, pRho, pGCap, pQ)
  for a in 0 .. n' {
    mem[cur] := n'
    mem[cur + 1] := a
    mem[cur + 2] := n'
    mem[cur + 3] := 0
    mem[cur + 4] := 0
    cur := cur + 5
  }
  for a in 0 .. 2 * mJ {
    mem[cur] := n' + 1
    mem[cur + 1] := n' + 1
    mem[cur + 2] := 1
    mem[cur + 3] := 0
    mem[cur + 4] := 0
    cur := cur + 5
  }
  for a in 0 .. n' {
    mem[cur] := a
    mem[cur + 1] := n'
    mem[cur + 2] := 1
    mem[cur + 3] := 0
    mem[cur + 4] := 0
    cur := cur + 5
  }
  return 0
}

private theorem negCost_sign' (c : ℤ) :
    (if -c < 0 then 1 else 0) = if 0 < c.natAbs then 1 - (if c < 0 then 1 else 0) else 0 := by
  split_ifs <;> omega

private theorem Qpos_edge_fwd (J : Circulation) (fwd rev : Fin J.m → Bool) (a : Fin J.m) :
    let Qpos := extractDualFromFlagsCall J fwd rev
    Qpos.solverEdgeWords ⟨a.val, by change a.val < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega⟩ =
      if fwd a then [(J.tail a).val, (J.head a).val, J.n + 1,
        if J.cost a < 0 then 1 else 0, (J.cost a).natAbs]
      else [J.n + 1, J.n + 1, 1, 0, 0] := by
  dsimp only [Circulation.solverEdgeWords, extractDualFromFlagsCall, Circulation.positiveInstance,
    Circulation.residual, Circulation.shortestRoutingGraph, Circulation.shortestRoutingStart,
    flagResidualGraph]
  have h1 : (⟨a.val, by omega⟩ : Fin (((J.m + J.m) + J.n) + ((J.m + J.m) + J.n))) =
      Fin.castAdd ((J.m + J.m) + J.n) (Fin.castAdd J.n (Fin.castAdd J.m a)) := by ext; rfl
  rw [h1]
  simp only [Fin.addCases_left]
  cases fwd a <;> simp

private theorem Qpos_edge_rev (J : Circulation) (fwd rev : Fin J.m → Bool) (a : Fin J.m) :
    let Qpos := extractDualFromFlagsCall J fwd rev
    Qpos.solverEdgeWords ⟨J.m + a.val, by change J.m + a.val < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega⟩ =
      if rev a then [(J.head a).val, (J.tail a).val, J.n + 1,
        if -J.cost a < 0 then 1 else 0, (J.cost a).natAbs]
      else [J.n + 1, J.n + 1, 1, 0, 0] := by
  dsimp only [Circulation.solverEdgeWords, extractDualFromFlagsCall, Circulation.positiveInstance,
    Circulation.residual, Circulation.shortestRoutingGraph, Circulation.shortestRoutingStart,
    flagResidualGraph]
  have h1 : (⟨J.m + a.val, by omega⟩ : Fin (((J.m + J.m) + J.n) + ((J.m + J.m) + J.n))) =
      Fin.castAdd ((J.m + J.m) + J.n) (Fin.castAdd J.n (Fin.natAdd J.m a)) := by ext; simp [Fin.natAdd]
  rw [h1]
  simp only [Fin.addCases_left, Fin.addCases_right]
  cases rev a <;> simp

private theorem Qpos_edge_srcFwd (J : Circulation) (hn : 0 < J.n)
    (fwd rev : Fin J.m → Bool) (v : Fin J.n) :
    let Qpos := extractDualFromFlagsCall J fwd rev
    Qpos.solverEdgeWords ⟨J.m + J.m + v.val, by change J.m + J.m + v.val < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega⟩ =
      [J.n, v.val, J.n, 0, 0] := by
  dsimp only [Circulation.solverEdgeWords, extractDualFromFlagsCall, Circulation.positiveInstance,
    Circulation.residual, Circulation.shortestRoutingGraph, Circulation.shortestRoutingStart,
    flagResidualGraph]
  have h1 : (⟨J.m + J.m + v.val, by omega⟩ : Fin (((J.m + J.m) + J.n) + ((J.m + J.m) + J.n))) =
      Fin.castAdd ((J.m + J.m) + J.n) (Fin.natAdd (J.m + J.m) v) := by ext; simp [Fin.natAdd]
  rw [h1]
  simp only [Fin.addCases_left, Fin.addCases_right]
  have hne : J.n ≠ 0 := by omega
  simp [hne]

private theorem Qpos_edge_revDummy (J : Circulation) (fwd rev : Fin J.m → Bool)
    (i : ℕ) (hi : i < 2 * J.m) :
    let Qpos := extractDualFromFlagsCall J fwd rev
    Qpos.solverEdgeWords ⟨J.m + J.m + J.n + i, by change J.m + J.m + J.n + i < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega⟩ =
      [J.n + 1, J.n + 1, 1, 0, 0] := by
  dsimp only [Circulation.solverEdgeWords, extractDualFromFlagsCall, Circulation.positiveInstance,
    Circulation.residual, Circulation.shortestRoutingGraph, Circulation.shortestRoutingStart,
    flagResidualGraph]
  have h1 : (⟨J.m + J.m + J.n + i, by omega⟩ : Fin (((J.m + J.m) + J.n) + ((J.m + J.m) + J.n))) =
      Fin.natAdd ((J.m + J.m) + J.n) (Fin.castAdd J.n ⟨i, by omega⟩) := by ext; simp [Fin.natAdd]
  rw [h1]
  simp only [Fin.addCases_right, Fin.addCases_left, Int.toNat_zero, ↓reduceIte, Fin.val_last,
    lt_irrefl, Int.natAbs_zero]

private theorem Qpos_edge_srcRev (J : Circulation) (fwd rev : Fin J.m → Bool) (v : Fin J.n) :
    let Qpos := extractDualFromFlagsCall J fwd rev
    Qpos.solverEdgeWords ⟨J.m + J.m + J.n + 2 * J.m + v.val,
        by change J.m + J.m + J.n + 2 * J.m + v.val < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega⟩ =
      [v.val, J.n, 1, 0, 0] := by
  dsimp only [Circulation.solverEdgeWords, extractDualFromFlagsCall, Circulation.positiveInstance,
    Circulation.residual, Circulation.shortestRoutingGraph, Circulation.shortestRoutingStart,
    flagResidualGraph]
  have h1 : (⟨J.m + J.m + J.n + 2 * J.m + v.val, by omega⟩ : Fin (((J.m + J.m) + J.n) + ((J.m + J.m) + J.n))) =
      Fin.natAdd ((J.m + J.m) + J.n) (Fin.natAdd (J.m + J.m) v) := by
    ext; simp [Fin.natAdd]; omega
  rw [h1]
  simp only [Fin.addCases_right, Int.toNat_one]
  simp

/-- Specification of `stage1WriteQEdges`. -/
def stage1WriteQEdgesSpec (w : ℕ) : Spec Stage1DualGraphIn where
  pre := fun g args =>
    ⨆ (pT : ℕ) (pH : ℕ) (pCS : ℕ) (pCM : ℕ) (pRho : ℕ) (pGCap : ℕ) (pQ : ℕ),
      ⌜args = [g.J.n, g.J.m, pT, pH, pCS, pCM, pRho, pGCap, pQ] ∧
        g.rho.length = g.J.m ∧ g.gCap.length = g.J.m ∧
        pQ + 2 + 2 * g.J.m * 5 < 2 ^ w ∧ g.J.n + 1 < 2 ^ w ∧ 5 < 2 ^ w⌝ *
      Assn.list pT (List.ofFn fun a : Fin g.J.m => (g.J.tail a).val) *
      Assn.list pH (List.ofFn fun a : Fin g.J.m => (g.J.head a).val) *
      Assn.list pCS (List.ofFn fun a : Fin g.J.m => if g.J.cost a < 0 then 1 else 0) *
      Assn.list pCM (List.ofFn fun a : Fin g.J.m => (g.J.cost a).natAbs) *
      Assn.list pRho g.rho *
      Assn.list pGCap g.gCap *
      (∏ i ∈ Finset.range g.J.m, Assn.list (pQ + 2 + i * 5) (List.replicate 5 0)) *
      (∏ i ∈ Finset.range g.J.m, Assn.list (pQ + 2 + (g.J.m + i) * 5) (List.replicate 5 0))
  post := fun g args cur =>
    ⨆ (pT : ℕ) (pH : ℕ) (pCS : ℕ) (pCM : ℕ) (pRho : ℕ) (pGCap : ℕ) (pQ : ℕ),
      let Qpos := extractDualFromFlagsCall g.J (dualFwdFlags g.J g.rho) (dualRevFlags g.J g.gCap)
      ⌜args = [g.J.n, g.J.m, pT, pH, pCS, pCM, pRho, pGCap, pQ] ∧
        cur = pQ + 2 + (g.J.m + g.J.m) * 5⌝ *
      Assn.list pT (List.ofFn fun a : Fin g.J.m => (g.J.tail a).val) *
      Assn.list pH (List.ofFn fun a : Fin g.J.m => (g.J.head a).val) *
      Assn.list pCS (List.ofFn fun a : Fin g.J.m => if g.J.cost a < 0 then 1 else 0) *
      Assn.list pCM (List.ofFn fun a : Fin g.J.m => (g.J.cost a).natAbs) *
      Assn.list pRho g.rho *
      Assn.list pGCap g.gCap *
      (∏ i ∈ Finset.range g.J.m, Assn.list (pQ + 2 + i * 5)
        (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else [])) *
      (∏ i ∈ Finset.range g.J.m, Assn.list (pQ + 2 + (g.J.m + i) * 5)
        (if h : g.J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨g.J.m + i, h⟩ else []))

theorem stage1WriteQEdges_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1WriteQEdges) :
    Meets w p f ((stage1WriteQEdgesSpec w).withCost fun g _ => 210 * g.J.m + 60) := by
  sep_enter g with hrho hgcap hpQ_fit hn1 hw5
  obtain ⟨J, rho, gCap⟩ := g
  dsimp only at hrho hgcap hpQ_fit hn1 hw5 ⊢
  set fwd := dualFwdFlags J rho
  set rev := dualRevFlags J gCap
  set Qpos := extractDualFromFlagsCall J fwd rev with hQ_def
  sep_step
  -- Loop 1: forward edges `0 .. J.m`
  sep_for (fun a (t : ℕ × ℕ × ℕ × ℕ × ℕ) =>
    ⟨[J.n, J.m, pT, pH, pCS, pCM, pRho, pGCap, pQ, pQ + 2 + a * 5, a,
      t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2, 0],
      a ≤ J.m, 85 * (J.m - a) + (110 * J.m + 30),
      [Assn.list pT (List.ofFn fun e : Fin J.m => (J.tail e).val),
       Assn.list pH (List.ofFn fun e : Fin J.m => (J.head e).val),
       Assn.list pCS (List.ofFn fun e : Fin J.m => if J.cost e < 0 then 1 else 0),
       Assn.list pCM (List.ofFn fun e : Fin J.m => (J.cost e).natAbs),
       Assn.list pRho rho,
       Assn.list pGCap gCap,
       ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + i * 5)
         (if i < a then (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else [])
          else List.replicate 5 0),
       ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + (J.m + i) * 5) (List.replicate 5 0)]⟩)
    with ⟨t0, t1, t2, t3, t4⟩
  · have hmem : a ∈ Finset.range J.m := Finset.mem_range.mpr hhi
    have hcur_next : pQ + 2 + a * 5 + 5 = pQ + 2 + (a + 1) * 5 := by omega
    have hcur_lt : pQ + 2 + (a + 1) * 5 < 2 ^ w := by omega
    have hr_a : rho[a]'(by omega) = rho.getD a 0 := (List.getD_eq_getElem _ _ (by omega)).symm
    have ht_a : (List.ofFn fun e : Fin J.m => (J.tail e).val)[a]'(by simp; omega) =
        (J.tail ⟨a, hhi⟩).val := List.getElem_ofFn ..
    have hh_a : (List.ofFn fun e : Fin J.m => (J.head e).val)[a]'(by simp; omega) =
        (J.head ⟨a, hhi⟩).val := List.getElem_ofFn ..
    have hcs_a : (List.ofFn fun e : Fin J.m => if J.cost e < 0 then 1 else 0)[a]'(by simp; omega) =
        if J.cost ⟨a, hhi⟩ < 0 then 1 else 0 := List.getElem_ofFn ..
    have hcm_a : (List.ofFn fun e : Fin J.m => (J.cost e).natAbs)[a]'(by simp; omega) =
        (J.cost ⟨a, hhi⟩).natAbs := List.getElem_ofFn ..
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun i => Assn.list (pQ + 2 + i * 5)
        (if i < a then (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else [])
         else List.replicate 5 0))
    have hnotlt : (if a < a then (if h : a < Qpos.m then Qpos.solverEdgeWords ⟨a, h⟩ else [])
        else List.replicate 5 0) = List.replicate 5 0 := by simp
    rw [hnotlt]
    have hqe := Qpos_edge_fwd J fwd rev ⟨a, hhi⟩
    have hupd : ∀ w_list : List ℕ,
        w_list = Qpos.solverEdgeWords ⟨a, by change a < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega⟩ →
        Assn.list (pQ + 2 + a * 5) w_list *
        (∏ i ∈ (Finset.range J.m).erase a, Assn.list (pQ + 2 + i * 5)
          (if i < a then (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else [])
           else List.replicate 5 0)) =
        ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + i * 5)
          (if i < a + 1 then (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else [])
           else List.replicate 5 0) := by
      intro w_list hw_eq; rw [hw_eq, Assn.prod_eq_mul_erase hmem]
      simp only [Nat.lt_succ_self, ↓reduceIte,
        show a < Qpos.m by change a < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega, ↓reduceDIte]
      congr 1; refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ a := (Finset.mem_erase.mp hi).1
      simp only [show (i < a) ↔ (i < a + 1) by omega]
    by_cases hpos : 0 < rho.getD a 0
    · have hfwd_t : fwd ⟨a, hhi⟩ = true := by unfold fwd dualFwdFlags; exact decide_eq_true hpos
      sep_step
      sep_step
      · sep_step; rw [ht_a] at ht; subst ht
        sep_step; rw [hh_a] at hh; subst hh
        sep_step; rw [hcs_a] at hcs; subst hcs
        sep_step; rw [hcm_a] at hcm; subst hcm
        iterate 5 sep_step
        sep_apply hupd _ (by rw [hqe, hfwd_t]; simp)
        sep_run
    · have hfwd_f : fwd ⟨a, hhi⟩ = false := by unfold fwd dualFwdFlags; exact decide_eq_false hpos
      sep_step
      sep_step
      · iterate 5 sep_step
        sep_apply hupd _ (by rw [hqe, hfwd_f]; simp)
        sep_run
  have hL1_end :
      (∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + i * 5)
        (if i < J.m then (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else [])
         else List.replicate 5 0)) =
      ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + i * 5)
        (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else []) :=
    Finset.prod_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
  rw [hL1_end]
  -- Loop 2: reverse edges `0 .. J.m`
  sep_for (fun a (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
    ⟨[J.n, J.m, pT, pH, pCS, pCM, pRho, pGCap, pQ, pQ + 2 + (J.m + a) * 5, a,
      t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2],
      a ≤ J.m, 95 * (J.m - a) + 10,
      [Assn.list pT (List.ofFn fun e : Fin J.m => (J.tail e).val),
       Assn.list pH (List.ofFn fun e : Fin J.m => (J.head e).val),
       Assn.list pCS (List.ofFn fun e : Fin J.m => if J.cost e < 0 then 1 else 0),
       Assn.list pCM (List.ofFn fun e : Fin J.m => (J.cost e).natAbs),
       Assn.list pRho rho,
       Assn.list pGCap gCap,
       ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + i * 5)
         (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else []),
       ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + (J.m + i) * 5)
         (if i < a then (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else [])
          else List.replicate 5 0)]⟩)
    with ⟨t0, t1, t2, t3, t4, t5⟩
  · have hmem : a ∈ Finset.range J.m := Finset.mem_range.mpr hhi
    have hcur_next : pQ + 2 + (J.m + a) * 5 + 5 = pQ + 2 + (J.m + (a + 1)) * 5 := by omega
    have hcur_lt : pQ + 2 + (J.m + (a + 1)) * 5 < 2 ^ w := by omega
    have hg_a : gCap[a]'(by omega) = gCap.getD a 0 := (List.getD_eq_getElem _ _ (by omega)).symm
    have ht_a : (List.ofFn fun e : Fin J.m => (J.tail e).val)[a]'(by simp; omega) =
        (J.tail ⟨a, hhi⟩).val := List.getElem_ofFn ..
    have hh_a : (List.ofFn fun e : Fin J.m => (J.head e).val)[a]'(by simp; omega) =
        (J.head ⟨a, hhi⟩).val := List.getElem_ofFn ..
    have hcm_a : (List.ofFn fun e : Fin J.m => (J.cost e).natAbs)[a]'(by simp; omega) =
        (J.cost ⟨a, hhi⟩).natAbs := List.getElem_ofFn ..
    have hcs_a : (List.ofFn fun e : Fin J.m => if J.cost e < 0 then 1 else 0)[a]'(by simp; omega) =
        if J.cost ⟨a, hhi⟩ < 0 then 1 else 0 := List.getElem_ofFn ..
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun i => Assn.list (pQ + 2 + (J.m + i) * 5)
        (if i < a then (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else [])
         else List.replicate 5 0))
    have hnotlt : (if a < a then (if h : J.m + a < Qpos.m then Qpos.solverEdgeWords ⟨J.m + a, h⟩ else [])
        else List.replicate 5 0) = List.replicate 5 0 := by simp
    rw [hnotlt]
    have hqe := Qpos_edge_rev J fwd rev ⟨a, hhi⟩
    have hns := negCost_sign' (J.cost ⟨a, hhi⟩)
    have hupd : ∀ w_list : List ℕ,
        w_list = Qpos.solverEdgeWords ⟨J.m + a, by change J.m + a < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega⟩ →
        Assn.list (pQ + 2 + (J.m + a) * 5) w_list *
        (∏ i ∈ (Finset.range J.m).erase a, Assn.list (pQ + 2 + (J.m + i) * 5)
          (if i < a then (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else [])
           else List.replicate 5 0)) =
        ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + (J.m + i) * 5)
          (if i < a + 1 then (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else [])
           else List.replicate 5 0) := by
      intro w_list hw_eq; rw [hw_eq, Assn.prod_eq_mul_erase hmem]
      simp only [Nat.lt_succ_self, ↓reduceIte,
        show J.m + a < Qpos.m by change J.m + a < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega, ↓reduceDIte]
      congr 1; refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ a := (Finset.mem_erase.mp hi).1
      simp only [show (i < a) ↔ (i < a + 1) by omega]
    by_cases hpos : 0 < gCap.getD a 0
    · have hrev_t : rev ⟨a, hhi⟩ = true := by unfold rev dualRevFlags; exact decide_eq_true hpos
      sep_step
      sep_step
      · sep_step; rw [ht_a] at ht; subst ht
        sep_step; rw [hh_a] at hh; subst hh
        sep_step; rw [hcs_a] at hcs; subst hcs
        sep_step; rw [hcm_a] at hcm; subst hcm
        sep_step
        by_cases hcm0 : 0 < (J.cost ⟨a, hhi⟩).natAbs
        · sep_step
          · iterate 6 sep_step
            sep_apply hupd _ (by rw [hqe, hrev_t, hns]; simp [hcm0, hns_1])
            sep_run
        · sep_step
          · have hcm_eq : (J.cost ⟨a, hhi⟩).natAbs = 0 := by omega
            iterate 6 sep_step
            sep_apply hupd _ (by rw [hqe, hrev_t, hns]; simp [hcm_eq])
            sep_run
    · have hrev_f : rev ⟨a, hhi⟩ = false := by unfold rev dualRevFlags; exact decide_eq_false hpos
      sep_step
      sep_step
      · iterate 5 sep_step
        sep_apply hupd _ (by rw [hqe, hrev_f]; simp)
        sep_run
  have hL2_end :
      (∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + (J.m + i) * 5)
        (if i < J.m then (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else [])
         else List.replicate 5 0)) =
      ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + (J.m + i) * 5)
        (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else []) :=
    Finset.prod_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
  rw [hL2_end]
  sep_run

/-! ### 2. Full `Qpos.solverWords` writer (`stage1WriteQ`) -/

/-- Specification of `stage1WriteQ`. -/
def stage1WriteQSpec (w : ℕ) : Spec Stage1DualGraphIn where
  pre := fun g args =>
    ⨆ (pT : ℕ) (pH : ℕ) (pCS : ℕ) (pCM : ℕ) (pRho : ℕ) (pGCap : ℕ) (pQ : ℕ),
      let Qpos := extractDualFromFlagsCall g.J (dualFwdFlags g.J g.rho) (dualRevFlags g.J g.gCap)
      ⌜args = [g.J.n, g.J.m, pT, pH, pCS, pCM, pRho, pGCap, pQ] ∧
        0 < g.J.n ∧ g.rho.length = g.J.m ∧ g.gCap.length = g.J.m ∧
        pQ + Qpos.solverWords.length < 2 ^ w ∧
        4 * g.J.m + 2 * g.J.n < 2 ^ w ∧ g.J.n + 2 < 2 ^ w ∧ 5 < 2 ^ w⌝ *
      Assn.list pT (List.ofFn fun a : Fin g.J.m => (g.J.tail a).val) *
      Assn.list pH (List.ofFn fun a : Fin g.J.m => (g.J.head a).val) *
      Assn.list pCS (List.ofFn fun a : Fin g.J.m => if g.J.cost a < 0 then 1 else 0) *
      Assn.list pCM (List.ofFn fun a : Fin g.J.m => (g.J.cost a).natAbs) *
      Assn.list pRho g.rho *
      Assn.list pGCap g.gCap *
      Assn.free pQ Qpos.solverWords.length
  post := fun g args v =>
    ⨆ (pT : ℕ) (pH : ℕ) (pCS : ℕ) (pCM : ℕ) (pRho : ℕ) (pGCap : ℕ) (pQ : ℕ),
      let Qpos := extractDualFromFlagsCall g.J (dualFwdFlags g.J g.rho) (dualRevFlags g.J g.gCap)
      ⌜args = [g.J.n, g.J.m, pT, pH, pCS, pCM, pRho, pGCap, pQ] ∧ v = 0⌝ *
      Assn.list pT (List.ofFn fun a : Fin g.J.m => (g.J.tail a).val) *
      Assn.list pH (List.ofFn fun a : Fin g.J.m => (g.J.head a).val) *
      Assn.list pCS (List.ofFn fun a : Fin g.J.m => if g.J.cost a < 0 then 1 else 0) *
      Assn.list pCM (List.ofFn fun a : Fin g.J.m => (g.J.cost a).natAbs) *
      Assn.list pRho g.rho *
      Assn.list pGCap g.gCap *
      Assn.list pQ Qpos.solverWords

private def dualQInputs (J : Circulation) (rho gCap : List ℕ)
    (pT pH pCS pCM pRho pGCap : ℕ) : Assn :=
  Assn.list pT (List.ofFn fun a : Fin J.m => (J.tail a).val) *
  Assn.list pH (List.ofFn fun a : Fin J.m => (J.head a).val) *
  Assn.list pCS (List.ofFn fun a : Fin J.m => if J.cost a < 0 then 1 else 0) *
  Assn.list pCM (List.ofFn fun a : Fin J.m => (J.cost a).natAbs) *
  Assn.list pRho rho *
  Assn.list pGCap gCap

private theorem dualQInputs_eq (J : Circulation) (rho gCap : List ℕ)
    (pT pH pCS pCM pRho pGCap : ℕ) :
    Assn.list pT (List.ofFn fun a : Fin J.m => (J.tail a).val) *
    Assn.list pH (List.ofFn fun a : Fin J.m => (J.head a).val) *
    Assn.list pCS (List.ofFn fun a : Fin J.m => if J.cost a < 0 then 1 else 0) *
    Assn.list pCM (List.ofFn fun a : Fin J.m => (J.cost a).natAbs) *
    Assn.list pRho rho *
    Assn.list pGCap gCap =
    dualQInputs J rho gCap pT pH pCS pCM pRho pGCap := rfl

theorem stage1WriteQ_meets {w : ℕ} {p : Program} {f edgesIdx : ℕ}
    (hp : p.procs[f]? = some (stage1WriteQ edgesIdx))
    (hedges : Meets w p edgesIdx ((stage1WriteQEdgesSpec w).withCost fun g _ => 210 * g.J.m + 60)) :
    Meets w p f ((stage1WriteQSpec w).withCost fun g _ => 380 * g.J.m + 150 * g.J.n + 150) := by
  sep_enter g with hn_pos hrho hgcap hpQ_fit hQm_lt hn2 hw5
  obtain ⟨J, rho, gCap⟩ := g
  dsimp only at hn_pos hrho hgcap hpQ_fit hQm_lt hn2 hw5 ⊢
  set fwd := dualFwdFlags J rho
  set rev := dualRevFlags J gCap
  set Qpos := extractDualFromFlagsCall J fwd rev with hQ_def
  have hQlen : Qpos.solverWords.length = 2 + (J.m + J.m + J.n + 2 * J.m + J.n) * 5 := by
    rw [Qpos.solverWords_length]
    change 2 + 5 * (((J.m + J.m) + J.n) + ((J.m + J.m) + J.n)) = _; omega
  rw [hQlen] at hpQ_fit ⊢
  sep_apply free_split_solverWords5 (a := pQ) (n1 := J.m) (n2 := J.m) (n3 := J.n) (n4 := 2 * J.m) (n5 := J.n)
  sep_step; sep_step
  have hhdr_eq : ((List.replicate 2 0).set 0 (J.n + 2)).set 1 (4 * J.m + 2 * J.n) =
      [J.n + 2, 4 * J.m + 2 * J.n] := rfl
  rw [hhdr_eq]
  sep_step from ⟨J, rho, gCap⟩
  subst hcur
  sep_apply dualQInputs_eq J rho gCap pT pH pCS pCM pRho pGCap
  -- Loop 3: forward super-source arcs `0 .. J.n`
  sep_for (fun a =>
    ⟨[J.n, J.m, pT, pH, pCS, pCM, pRho, pGCap, pQ, pQ + 2 + (J.m + J.m + a) * 5, a],
      a ≤ J.n, 55 * (J.n - a) + (135 * J.m + 65 * J.n + 40),
      [dualQInputs J rho gCap pT pH pCS pCM pRho pGCap,
       Assn.list pQ [J.n + 2, 4 * J.m + 2 * J.n],
       ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + i * 5)
         (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else []),
       ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + (J.m + i) * 5)
         (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else []),
       ∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + i) * 5)
         (if i < a then (if h : J.m + J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])
          else List.replicate 5 0),
       ∏ i ∈ Finset.range (2 * J.m), Assn.list (pQ + 2 + (J.m + J.m + J.n + i) * 5) (List.replicate 5 0),
       ∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + i) * 5) (List.replicate 5 0)]⟩)
  · have hmem : a ∈ Finset.range J.n := Finset.mem_range.mpr hhi
    have hcur_next : pQ + 2 + (J.m + J.m + a) * 5 + 5 = pQ + 2 + (J.m + J.m + (a + 1)) * 5 := by omega
    have hcur_lt : pQ + 2 + (J.m + J.m + (a + 1)) * 5 < 2 ^ w := by omega
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun i => Assn.list (pQ + 2 + (J.m + J.m + i) * 5)
        (if i < a then (if h : J.m + J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])
         else List.replicate 5 0))
    have hnotlt : (if a < a then (if h : J.m + J.m + a < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + a, h⟩ else [])
        else List.replicate 5 0) = List.replicate 5 0 := by simp
    rw [hnotlt]
    have hqe := Qpos_edge_srcFwd J hn_pos fwd rev ⟨a, hhi⟩
    iterate 5 sep_step
    have hupd :
        Assn.list (pQ + 2 + (J.m + J.m + a) * 5) [J.n, a, J.n, 0, 0] *
        (∏ i ∈ (Finset.range J.n).erase a, Assn.list (pQ + 2 + (J.m + J.m + i) * 5)
          (if i < a then (if h : J.m + J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])
           else List.replicate 5 0)) =
        ∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + i) * 5)
          (if i < a + 1 then (if h : J.m + J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])
           else List.replicate 5 0) := by
      rw [← hqe, Assn.prod_eq_mul_erase hmem]
      simp only [Nat.lt_succ_self, ↓reduceIte,
        show J.m + J.m + a < Qpos.m by change J.m + J.m + a < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega, ↓reduceDIte]
      congr 1; refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ a := (Finset.mem_erase.mp hi).1
      simp only [show (i < a) ↔ (i < a + 1) by omega]
    sep_apply hupd; sep_run
  have hL3_end :
      (∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + i) * 5)
        (if i < J.n then (if h : J.m + J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])
         else List.replicate 5 0)) =
      ∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + i) * 5)
        (if h : J.m + J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + i, h⟩ else []) :=
    Finset.prod_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
  rw [hL3_end]
  -- Loop 4: reverse dummy loops `0 .. 2 * J.m`
  sep_for (fun a =>
    ⟨[J.n, J.m, pT, pH, pCS, pCM, pRho, pGCap, pQ, pQ + 2 + (J.m + J.m + J.n + a) * 5, a],
      a ≤ 2 * J.m, 55 * (2 * J.m - a) + (65 * J.n + 25),
      [dualQInputs J rho gCap pT pH pCS pCM pRho pGCap,
       Assn.list pQ [J.n + 2, 4 * J.m + 2 * J.n],
       ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + i * 5)
         (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else []),
       ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + (J.m + i) * 5)
         (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else []),
       ∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + i) * 5)
         (if h : J.m + J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + i, h⟩ else []),
       ∏ i ∈ Finset.range (2 * J.m), Assn.list (pQ + 2 + (J.m + J.m + J.n + i) * 5)
         (if i < a then (if h : J.m + J.m + J.n + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + i, h⟩ else [])
          else List.replicate 5 0),
       ∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + i) * 5) (List.replicate 5 0)]⟩)
  · have hmem : a ∈ Finset.range (2 * J.m) := Finset.mem_range.mpr hhi
    have hcur_next : pQ + 2 + (J.m + J.m + J.n + a) * 5 + 5 = pQ + 2 + (J.m + J.m + J.n + (a + 1)) * 5 := by omega
    have hcur_lt : pQ + 2 + (J.m + J.m + J.n + (a + 1)) * 5 < 2 ^ w := by omega
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun i => Assn.list (pQ + 2 + (J.m + J.m + J.n + i) * 5)
        (if i < a then (if h : J.m + J.m + J.n + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + i, h⟩ else [])
         else List.replicate 5 0))
    have hnotlt : (if a < a then (if h : J.m + J.m + J.n + a < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + a, h⟩ else [])
        else List.replicate 5 0) = List.replicate 5 0 := by simp
    rw [hnotlt]
    have hqe := Qpos_edge_revDummy J fwd rev a hhi
    iterate 5 sep_step
    have hupd :
        Assn.list (pQ + 2 + (J.m + J.m + J.n + a) * 5) [J.n + 1, J.n + 1, 1, 0, 0] *
        (∏ i ∈ (Finset.range (2 * J.m)).erase a, Assn.list (pQ + 2 + (J.m + J.m + J.n + i) * 5)
          (if i < a then (if h : J.m + J.m + J.n + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + i, h⟩ else [])
           else List.replicate 5 0)) =
        ∏ i ∈ Finset.range (2 * J.m), Assn.list (pQ + 2 + (J.m + J.m + J.n + i) * 5)
          (if i < a + 1 then (if h : J.m + J.m + J.n + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + i, h⟩ else [])
           else List.replicate 5 0) := by
      rw [← hqe, Assn.prod_eq_mul_erase hmem]
      simp only [Nat.lt_succ_self, ↓reduceIte,
        show J.m + J.m + J.n + a < Qpos.m by change J.m + J.m + J.n + a < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega, ↓reduceDIte]
      congr 1; refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ a := (Finset.mem_erase.mp hi).1
      simp only [show (i < a) ↔ (i < a + 1) by omega]
    sep_apply hupd; sep_run
  have hL4_end :
      (∏ i ∈ Finset.range (2 * J.m), Assn.list (pQ + 2 + (J.m + J.m + J.n + i) * 5)
        (if i < 2 * J.m then (if h : J.m + J.m + J.n + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + i, h⟩ else [])
         else List.replicate 5 0)) =
      ∏ i ∈ Finset.range (2 * J.m), Assn.list (pQ + 2 + (J.m + J.m + J.n + i) * 5)
        (if h : J.m + J.m + J.n + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + i, h⟩ else []) :=
    Finset.prod_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
  rw [hL4_end]
  -- Loop 5: reverse super-source arcs `0 .. J.n`
  sep_for (fun a =>
    ⟨[J.n, J.m, pT, pH, pCS, pCM, pRho, pGCap, pQ, pQ + 2 + (J.m + J.m + J.n + 2 * J.m + a) * 5, a],
      a ≤ J.n, 55 * (J.n - a) + 10,
      [dualQInputs J rho gCap pT pH pCS pCM pRho pGCap,
       Assn.list pQ [J.n + 2, 4 * J.m + 2 * J.n],
       ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + i * 5)
         (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else []),
       ∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + (J.m + i) * 5)
         (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else []),
       ∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + i) * 5)
         (if h : J.m + J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + i, h⟩ else []),
       ∏ i ∈ Finset.range (2 * J.m), Assn.list (pQ + 2 + (J.m + J.m + J.n + i) * 5)
         (if h : J.m + J.m + J.n + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + i, h⟩ else []),
       ∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + i) * 5)
         (if i < a then (if h : J.m + J.m + J.n + 2 * J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + 2 * J.m + i, h⟩ else [])
          else List.replicate 5 0)]⟩)
  · have hmem : a ∈ Finset.range J.n := Finset.mem_range.mpr hhi
    have hcur_next : pQ + 2 + (J.m + J.m + J.n + 2 * J.m + a) * 5 + 5 =
        pQ + 2 + (J.m + J.m + J.n + 2 * J.m + (a + 1)) * 5 := by omega
    have hcur_lt : pQ + 2 + (J.m + J.m + J.n + 2 * J.m + (a + 1)) * 5 < 2 ^ w := by omega
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun i => Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + i) * 5)
        (if i < a then (if h : J.m + J.m + J.n + 2 * J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + 2 * J.m + i, h⟩ else [])
         else List.replicate 5 0))
    have hnotlt : (if a < a then (if h : J.m + J.m + J.n + 2 * J.m + a < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + 2 * J.m + a, h⟩ else [])
        else List.replicate 5 0) = List.replicate 5 0 := by simp
    rw [hnotlt]
    have hqe := Qpos_edge_srcRev J fwd rev ⟨a, hhi⟩
    iterate 5 sep_step
    have hupd :
        Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + a) * 5) [a, J.n, 1, 0, 0] *
        (∏ i ∈ (Finset.range J.n).erase a, Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + i) * 5)
          (if i < a then (if h : J.m + J.m + J.n + 2 * J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + 2 * J.m + i, h⟩ else [])
           else List.replicate 5 0)) =
        ∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + i) * 5)
          (if i < a + 1 then (if h : J.m + J.m + J.n + 2 * J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + 2 * J.m + i, h⟩ else [])
           else List.replicate 5 0) := by
      rw [← hqe, Assn.prod_eq_mul_erase hmem]
      simp only [Nat.lt_succ_self, ↓reduceIte,
        show J.m + J.m + J.n + 2 * J.m + a < Qpos.m by change J.m + J.m + J.n + 2 * J.m + a < ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega, ↓reduceDIte]
      congr 1; refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ a := (Finset.mem_erase.mp hi).1
      simp only [show (i < a) ↔ (i < a + 1) by omega]
    sep_apply hupd; sep_run
  have hL5_end :
      (∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + i) * 5)
        (if i < J.n then (if h : J.m + J.m + J.n + 2 * J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + 2 * J.m + i, h⟩ else [])
         else List.replicate 5 0)) =
      ∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + i) * 5)
        (if h : J.m + J.m + J.n + 2 * J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + 2 * J.m + i, h⟩ else []) :=
    Finset.prod_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
  rw [hL5_end]
  have hmergeQ :
      Assn.list pQ [J.n + 2, 4 * J.m + 2 * J.n] *
      (∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + i * 5) (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else [])) *
      (∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + (J.m + i) * 5) (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else [])) *
      (∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + i) * 5) (if h : J.m + J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])) *
      (∏ i ∈ Finset.range (2 * J.m), Assn.list (pQ + 2 + (J.m + J.m + J.n + i) * 5) (if h : J.m + J.m + J.n + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + i, h⟩ else [])) *
      (∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + i) * 5) (if h : J.m + J.m + J.n + 2 * J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + 2 * J.m + i, h⟩ else [])) =
      Assn.list pQ Qpos.solverWords := by
    have hprod := (prod_split_five (n1 := J.m) (n2 := J.m) (n3 := J.n) (n4 := 2 * J.m) (n5 := J.n)
      (fun e => Assn.list (pQ + 2 + e * 5) (if h : e < Qpos.m then Qpos.solverEdgeWords ⟨e, h⟩ else []))).symm
    have hQm_eq : J.m + J.m + J.n + 2 * J.m + J.n = Qpos.m := by
      change _ = ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega
    have hQm_eq' : 4 * J.m + 2 * J.n = Qpos.m := by omega
    have hQn_eq : J.n + 2 = Qpos.n := rfl
    rw [hQm_eq] at hprod
    rw [hQn_eq, hQm_eq']
    have hreassoc :
        Assn.list pQ [Qpos.n, Qpos.m] *
        (∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + i * 5) (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else [])) *
        (∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + (J.m + i) * 5) (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else [])) *
        (∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + i) * 5) (if h : J.m + J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])) *
        (∏ i ∈ Finset.range (2 * J.m), Assn.list (pQ + 2 + (J.m + J.m + J.n + i) * 5) (if h : J.m + J.m + J.n + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + i, h⟩ else [])) *
        (∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + i) * 5) (if h : J.m + J.m + J.n + 2 * J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + 2 * J.m + i, h⟩ else [])) =
        Assn.list pQ [Qpos.n, Qpos.m] *
        ((∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + i * 5) (if h : i < Qpos.m then Qpos.solverEdgeWords ⟨i, h⟩ else [])) *
         (∏ i ∈ Finset.range J.m, Assn.list (pQ + 2 + (J.m + i) * 5) (if h : J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + i, h⟩ else [])) *
         (∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + i) * 5) (if h : J.m + J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + i, h⟩ else [])) *
         (∏ i ∈ Finset.range (2 * J.m), Assn.list (pQ + 2 + (J.m + J.m + J.n + i) * 5) (if h : J.m + J.m + J.n + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + i, h⟩ else [])) *
         (∏ i ∈ Finset.range J.n, Assn.list (pQ + 2 + (J.m + J.m + J.n + 2 * J.m + i) * 5) (if h : J.m + J.m + J.n + 2 * J.m + i < Qpos.m then Qpos.solverEdgeWords ⟨J.m + J.m + J.n + 2 * J.m + i, h⟩ else []))) := by
      ac_rfl
    rw [hreassoc, hprod]
    exact prod_solverEdgeWords_eq_list Qpos pQ
  sep_apply hmergeQ
  sep_apply (dualQInputs_eq J rho gCap pT pH pCS pCM pRho pGCap).symm
  sep_run

end MinCostFlow.NarrowProg.Stage1
