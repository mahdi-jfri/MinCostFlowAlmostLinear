module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Array
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1DualWrite
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Dual-extraction routing builder (`stage1BuildRouting`)

Builds `routing : Fin S.m → ℤ` (stored as nonnegative words at `pR`) from the bounded solver's
flow `pDual` on `Qpos = extractDualFromFlagsCall J fwd rev` and presence arrays `(pRho, pGCap)`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Scaling.Machine
  MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate

/-- Build `routing : Fin S.m → ℤ` (stored as nonnegative words at `pR`) from the bounded solver's
flow `pDual` on `Qpos` and presence arrays `(pRho, pGCap)`. -/
wram_def stage1BuildRouting (n', mJ, pRho, pGCap, pDual, pR) {
  for a in 0 .. mJ {
    f := mem[pRho + a]
    if 0 < f {
      v := mem[pDual + a]
      mem[pR + a] := v
    } else {
      mem[pR + a] := 0
    }
  }
  for a in 0 .. mJ {
    f := mem[pGCap + a]
    if 0 < f {
      v := mem[pDual + mJ + a]
      mem[pR + mJ + a] := v
    } else {
      mem[pR + mJ + a] := 0
    }
  }
  sm := 2 * mJ + n'
  for a in 0 .. n' {
    df := mem[pDual + 2 * mJ + a]
    dr := mem[pDual + sm + 2 * mJ + a]
    mem[pR + 2 * mJ + a] := 1 + df - dr
  }
  return 0
}

/-- The routing flow vector constructed in `extractDualFromFlagsOfAnswer`. -/
def dualRoutingOfAnswer (J : Circulation) (fwd rev : Fin J.m → Bool)
    (d_dual : Fin (extractDualFromFlagsCall J fwd rev).m → ℤ) :
    Fin (flagResidualGraph J fwd rev).shortestRoutingGraph.m → ℤ :=
  let R := flagResidualGraph J fwd rev
  let S := R.shortestRoutingGraph
  let start := R.shortestRoutingStart
  let Q := S.residual start
  let delta : Fin Q.m → ℤ := fun e => if Q.capacity e = 0 then 0 else d_dual e
  fun e => start e + delta (Fin.castAdd S.m e) - delta (Fin.natAdd S.m e)

structure Stage1BuildRoutingIn where
  J : Circulation
  rho : List ℕ
  gCap : List ℕ
  dFlow : List ℕ

def stage1BuildRoutingSpec (w : ℕ) : Spec Stage1BuildRoutingIn where
  pre := fun g args =>
    ⨆ (pRho : ℕ) (pGCap : ℕ) (pDual : ℕ) (pR : ℕ),
      let fwd := dualFwdFlags g.J g.rho
      let rev := dualRevFlags g.J g.gCap
      let S := (flagResidualGraph g.J fwd rev).shortestRoutingGraph
      let Qpos := extractDualFromFlagsCall g.J fwd rev
      ⌜args = [g.J.n, g.J.m, pRho, pGCap, pDual, pR] ∧
        0 < g.J.n ∧ g.rho.length = g.J.m ∧ g.gCap.length = g.J.m ∧
        g.dFlow.length = Qpos.m ∧
        (∀ x ∈ g.dFlow, x < 2 ^ w) ∧
        (∀ v : Fin g.J.n,
          g.dFlow.getD (S.m + 2 * g.J.m + v.val) 0 ≤ 1 + g.dFlow.getD (2 * g.J.m + v.val) 0 ∧
          1 + g.dFlow.getD (2 * g.J.m + v.val) 0 < 2 ^ w) ∧
        2 * g.J.m + g.J.n < 2 ^ w ∧ 2 < 2 ^ w⌝ *
      Assn.list pRho g.rho *
      Assn.list pGCap g.gCap *
      Assn.list pDual g.dFlow *
      Assn.free pR S.m
  post := fun g args v =>
    ⨆ (pRho : ℕ) (pGCap : ℕ) (pDual : ℕ) (pR : ℕ),
      let fwd := dualFwdFlags g.J g.rho
      let rev := dualRevFlags g.J g.gCap
      let d_dual : Fin (extractDualFromFlagsCall g.J fwd rev).m → ℤ :=
        fun e => (g.dFlow.getD e.val 0 : ℤ)
      let routing := dualRoutingOfAnswer g.J fwd rev d_dual
      ⌜args = [g.J.n, g.J.m, pRho, pGCap, pDual, pR] ∧ v = 0 ∧
        (∀ e, 0 ≤ routing e ∧ (routing e).toNat < 2 ^ w)⌝ *
      Assn.list pRho g.rho *
      Assn.list pGCap g.gCap *
      Assn.list pDual g.dFlow *
      Assn.list pR (List.ofFn fun e => (routing e).toNat)

private theorem dualRoutingOfAnswer_fwd (J : Circulation) (fwd rev : Fin J.m → Bool)
    (dFlow : List ℕ) (a : Fin J.m) :
    dualRoutingOfAnswer J fwd rev (fun e => (dFlow.getD e.val 0 : ℤ))
      (Fin.castAdd J.n (Fin.castAdd J.m a)) =
    if fwd a then (dFlow.getD a.val 0 : ℤ) else 0 := by
  unfold dualRoutingOfAnswer
  simp only [Circulation.shortestRoutingGraph, Circulation.shortestRoutingStart, flagResidualGraph,
    Fin.addCases_left, Fin.addCases_right, Int.toNat_zero, ↓reduceIte, sub_zero, zero_add]
  cases fwd a <;> simp

private theorem dualRoutingOfAnswer_rev (J : Circulation) (fwd rev : Fin J.m → Bool)
    (dFlow : List ℕ) (a : Fin J.m) :
    dualRoutingOfAnswer J fwd rev (fun e => (dFlow.getD e.val 0 : ℤ))
      (Fin.castAdd J.n (Fin.natAdd J.m a)) =
    if rev a then (dFlow.getD (J.m + a.val) 0 : ℤ) else 0 := by
  unfold dualRoutingOfAnswer
  simp only [Circulation.shortestRoutingGraph, Circulation.shortestRoutingStart, flagResidualGraph,
    Fin.addCases_left, Fin.addCases_right, Int.toNat_zero, ↓reduceIte, sub_zero, zero_add]
  cases rev a <;> simp [Fin.val_castAdd, Nat.add_comm]

private theorem dualRoutingOfAnswer_super (J : Circulation) (hn : 0 < J.n)
    (fwd rev : Fin J.m → Bool) (dFlow : List ℕ) (v : Fin J.n) :
    dualRoutingOfAnswer J fwd rev (fun e => (dFlow.getD e.val 0 : ℤ))
      (Fin.natAdd (J.m + J.m) v) =
    1 + (dFlow.getD (2 * J.m + v.val) 0 : ℤ) -
      (dFlow.getD ((J.m + J.m + J.n) + 2 * J.m + v.val) 0 : ℤ) := by
  unfold dualRoutingOfAnswer
  simp only [Circulation.shortestRoutingGraph, Circulation.shortestRoutingStart, flagResidualGraph,
    Fin.addCases_left, Fin.addCases_right]
  have hsub : ((((J.n + 1 : ℕ) : ℤ) - 1).toNat) = J.n := by omega
  have hne : J.n ≠ 0 := by omega
  have h1 : (Fin.castAdd (J.m + J.m + J.n) (Fin.natAdd (J.m + J.m) v)).val = 2 * J.m + v.val := by
    simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
  have h2 : (Fin.natAdd (J.m + J.m + J.n) (Fin.natAdd (J.m + J.m) v)).val =
      (J.m + J.m + J.n) + 2 * J.m + v.val := by
    simp only [Fin.val_natAdd]; omega
  simp only [hsub, hne, ↓reduceIte, Int.toNat_one, Nat.one_ne_zero, h1, h2]

private theorem dualRouting_list_eq (J : Circulation) (hn : 0 < J.n)
    (fwd rev : Fin J.m → Bool) (dFlow : List ℕ)
    (hdbnd : ∀ v : Fin J.n,
      dFlow.getD ((J.m + J.m + J.n) + 2 * J.m + v.val) 0 ≤ 1 + dFlow.getD (2 * J.m + v.val) 0) :
    (List.ofFn fun a : Fin J.m => if fwd a then dFlow.getD a.val 0 else 0) ++
    (List.ofFn fun a : Fin J.m => if rev a then dFlow.getD (J.m + a.val) 0 else 0) ++
    (List.ofFn fun v : Fin J.n =>
      1 + dFlow.getD (2 * J.m + v.val) 0 - dFlow.getD ((J.m + J.m + J.n) + 2 * J.m + v.val) 0) =
    List.ofFn fun e =>
      (dualRoutingOfAnswer J fwd rev (fun a => (dFlow.getD a.val 0 : ℤ)) e).toNat := by
  have hSm : (flagResidualGraph J fwd rev).shortestRoutingGraph.m = J.m + J.m + J.n := rfl
  refine List.ext_getElem (by simp; omega) fun i hi1 hi2 => ?_
  have hiS : i < (flagResidualGraph J fwd rev).shortestRoutingGraph.m := by
    simp only [List.length_append, List.length_ofFn] at hi1; omega
  rw [List.getElem_ofFn]
  by_cases h1 : i < J.m
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_ofFn]
    have he : (⟨i, hiS⟩ : Fin _) = Fin.castAdd J.n (Fin.castAdd J.m ⟨i, h1⟩) := by ext; rfl
    rw [he, dualRoutingOfAnswer_fwd]
    cases fwd ⟨i, h1⟩ <;> simp
  · by_cases h2 : i < 2 * J.m
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem_ofFn]
      have hi' : i - J.m < J.m := by omega
      have he : (⟨i, hiS⟩ : Fin _) = Fin.castAdd J.n (Fin.natAdd J.m ⟨i - J.m, hi'⟩) := by
        ext; simp; omega
      rw [he, dualRoutingOfAnswer_rev]
      cases rev ⟨i - J.m, hi'⟩ <;> simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_append, List.length_ofFn, List.getElem_ofFn]
      have hi' : i - (J.m + J.m) < J.n := by omega
      have he : (⟨i, hiS⟩ : Fin _) = Fin.natAdd (J.m + J.m) ⟨i - (J.m + J.m), hi'⟩ := by
        ext; simp; omega
      rw [he, dualRoutingOfAnswer_super J hn]
      have hb := hdbnd ⟨i - (J.m + J.m), hi'⟩
      dsimp only at hb ⊢
      omega

private theorem dualRouting_bounds {w : ℕ} (J : Circulation) (hn : 0 < J.n)
    (fwd rev : Fin J.m → Bool) (dFlow : List ℕ)
    (hdlen : dFlow.length = (extractDualFromFlagsCall J fwd rev).m)
    (hdf_lt : ∀ x ∈ dFlow, x < 2 ^ w)
    (hdbnd : ∀ v : Fin J.n,
      dFlow.getD ((J.m + J.m + J.n) + 2 * J.m + v.val) 0 ≤ 1 + dFlow.getD (2 * J.m + v.val) 0 ∧
      1 + dFlow.getD (2 * J.m + v.val) 0 < 2 ^ w) :
    ∀ e, 0 ≤ dualRoutingOfAnswer J fwd rev (fun a => (dFlow.getD a.val 0 : ℤ)) e ∧
      (dualRoutingOfAnswer J fwd rev (fun a => (dFlow.getD a.val 0 : ℤ)) e).toNat < 2 ^ w := by
  have hQm : (extractDualFromFlagsCall J fwd rev).m =
      (J.m + J.m + J.n) + (J.m + J.m + J.n) := rfl
  intro e
  refine Fin.addCases (m := J.m + J.m) (n := J.n) (fun e1 => ?_) (fun v => ?_) e
  · refine Fin.addCases (m := J.m) (n := J.m) (fun a => ?_) (fun a => ?_) e1
    · rw [dualRoutingOfAnswer_fwd]
      cases fwd a
      · simp
      · simp only [↓reduceIte, Nat.cast_nonneg, Int.toNat_natCast, true_and]
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact hdf_lt _ (List.getElem_mem _)
    · rw [dualRoutingOfAnswer_rev]
      cases rev a
      · simp
      · simp only [↓reduceIte, Nat.cast_nonneg, Int.toNat_natCast, true_and]
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact hdf_lt _ (List.getElem_mem _)
  · rw [dualRoutingOfAnswer_super J hn]
    have hb := hdbnd v
    omega

@[irreducible] private def rMix (a b : List ℕ) (k : ℕ) : List ℕ := a.take k ++ b.drop k

private theorem rMix_zero (a b : List ℕ) : rMix a b 0 = b := by unfold rMix; simp

private theorem rMix_full {a b : List ℕ} {m : ℕ} (ha : a.length = m) (hb : b.length = m) :
    rMix a b m = a := by
  unfold rMix
  simp [List.take_of_length_le (by omega : a.length ≤ m),
    List.drop_of_length_le (by omega : b.length ≤ m)]

private theorem rMix_len {a b : List ℕ} {e m : ℕ} (ha : a.length = m) (hb : b.length = m)
    (he : e ≤ m) : (rMix a b e).length = m := by
  unfold rMix; simp [ha, hb]; omega

private theorem rMix_set {a b : List ℕ} {e m v : ℕ} (ha : a.length = m) (hb : b.length = m)
    (he : e < m) (hv : a[e]'(by omega) = v) :
    (rMix a b e).set e v = rMix a b (e + 1) := by
  unfold rMix
  exact set_take_append_drop (by omega) (by omega) hv

theorem stage1BuildRouting_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage1BuildRouting) :
    Meets w p f ((stage1BuildRoutingSpec w).withCost fun g _ => 110 * g.J.m + 60 * g.J.n + 80) := by
  sep_enter g with hn_pos hrho hgcap hdlen hdf_lt hdbnd hSm_lt hw2
  obtain ⟨J, rho, gCap, dFlow⟩ := g
  dsimp only at hn_pos hrho hgcap hdlen hdf_lt hdbnd hSm_lt hw2 ⊢
  set fwd := dualFwdFlags J rho
  set rev := dualRevFlags J gCap
  set S := (flagResidualGraph J fwd rev).shortestRoutingGraph
  set Qpos := extractDualFromFlagsCall J fwd rev
  have hSm_eq : S.m = J.m + J.m + J.n := rfl
  have hQm_eq : Qpos.m = (J.m + J.m + J.n) + (J.m + J.m + J.n) := rfl
  set r1 := List.ofFn fun a : Fin J.m => if fwd a then dFlow.getD a.val 0 else 0
  set r2 := List.ofFn fun a : Fin J.m => if rev a then dFlow.getD (J.m + a.val) 0 else 0
  set r3 := List.ofFn fun v : Fin J.n =>
    1 + dFlow.getD (2 * J.m + v.val) 0 - dFlow.getD ((J.m + J.m + J.n) + 2 * J.m + v.val) 0
  have hr1_len : r1.length = J.m := List.length_ofFn
  have hr2_len : r2.length = J.m := List.length_ofFn
  have hr3_len : r3.length = J.n := List.length_ofFn
  have hsplitR : Assn.free pR S.m =
      Assn.list pR (rMix r1 (List.replicate J.m 0) 0) *
      Assn.list (pR + J.m) (rMix r2 (List.replicate J.m 0) 0) *
      Assn.list (pR + 2 * J.m) (rMix r3 (List.replicate J.n 0) 0) := by
    rw [rMix_zero, rMix_zero, rMix_zero]
    have h1 : Assn.list pR (List.replicate J.m 0) = Assn.free pR J.m := rfl
    have h2 : Assn.list (pR + J.m) (List.replicate J.m 0) = Assn.free (pR + J.m) J.m := rfl
    have h3 : Assn.list (pR + 2 * J.m) (List.replicate J.n 0) = Assn.free (pR + 2 * J.m) J.n := rfl
    rw [h1, h2, h3, ← Assn.free_add', show pR + 2 * J.m = pR + (J.m + J.m) by omega, ← Assn.free_add']
  sep_apply hsplitR
  -- Loop 1: `0 .. J.m`
  sep_for (fun a (t : ℕ × ℕ) =>
    ⟨[J.n, J.m, pRho, pGCap, pDual, pR, a, t.1, t.2, 0, 0, 0],
      a ≤ J.m, 45 * (J.m - a) + (55 * J.m + 55 * J.n + 50),
      [Assn.list pRho rho, Assn.list pGCap gCap, Assn.list pDual dFlow,
       Assn.list pR (rMix r1 (List.replicate J.m 0) a),
       Assn.list (pR + J.m) (rMix r2 (List.replicate J.m 0) 0),
       Assn.list (pR + 2 * J.m) (rMix r3 (List.replicate J.n 0) 0)]⟩)
    with ⟨t0, t1⟩
  · have hle : a ≤ J.m := Nat.le_of_lt hhi
    have hlen := rMix_len hr1_len (List.length_replicate (n := J.m) (a := 0)) hle
    have hr_a : rho[a]'(by omega) = rho.getD a 0 := (List.getD_eq_getElem _ _ (by omega)).symm
    have hd_a : dFlow[a]'(by omega) = dFlow.getD a 0 := (List.getD_eq_getElem _ _ (by omega)).symm
    by_cases hpos : 0 < rho.getD a 0
    · have hft : fwd ⟨a, hhi⟩ = true := by unfold fwd dualFwdFlags; exact decide_eq_true hpos
      sep_step
      sep_step
      · sep_step
        sep_run
        rw [hd_a]
        exact rMix_set hr1_len List.length_replicate hhi (by simp [r1, hft])
    · have hff : fwd ⟨a, hhi⟩ = false := by unfold fwd dualFwdFlags; exact decide_eq_false hpos
      sep_step
      sep_step
      · sep_run
        exact rMix_set hr1_len List.length_replicate hhi (by simp [r1, hff])
  rw [rMix_full hr1_len List.length_replicate]
  -- Loop 2: `0 .. J.m`
  sep_for (fun a (t : ℕ × ℕ) =>
    ⟨[J.n, J.m, pRho, pGCap, pDual, pR, a, t.1, t.2, 0, 0, 0],
      a ≤ J.m, 45 * (J.m - a) + (55 * J.n + 35),
      [Assn.list pRho rho, Assn.list pGCap gCap, Assn.list pDual dFlow,
       Assn.list pR r1,
       Assn.list (pR + J.m) (rMix r2 (List.replicate J.m 0) a),
       Assn.list (pR + 2 * J.m) (rMix r3 (List.replicate J.n 0) 0)]⟩)
    with ⟨t0, t1⟩
  · have hle : a ≤ J.m := Nat.le_of_lt hhi
    have hlen := rMix_len hr2_len (List.length_replicate (n := J.m) (a := 0)) hle
    have hg_a : gCap[a]'(by omega) = gCap.getD a 0 := (List.getD_eq_getElem _ _ (by omega)).symm
    have hd_a : dFlow[J.m + a]'(by omega) = dFlow.getD (J.m + a) 0 :=
      (List.getD_eq_getElem _ _ (by omega)).symm
    by_cases hpos : 0 < gCap.getD a 0
    · have hrt : rev ⟨a, hhi⟩ = true := by unfold rev dualRevFlags; exact decide_eq_true hpos
      sep_step
      sep_step
      · sep_step
        sep_run
        rw [hv, hd_a]
        exact rMix_set hr2_len List.length_replicate hhi (by simp [r2, hrt])
    · have hrf : rev ⟨a, hhi⟩ = false := by unfold rev dualRevFlags; exact decide_eq_false hpos
      sep_step
      sep_step
      · sep_run
        exact rMix_set hr2_len List.length_replicate hhi (by simp [r2, hrf])
  rw [rMix_full hr2_len List.length_replicate]
  sep_step
  -- Loop 3: `0 .. J.n`
  sep_for (fun a (t : ℕ × ℕ) =>
    ⟨[J.n, J.m, pRho, pGCap, pDual, pR, a, t0, t1, 2 * J.m + J.n, t.1, t.2],
      a ≤ J.n, 45 * (J.n - a) + 10,
      [Assn.list pRho rho, Assn.list pGCap gCap, Assn.list pDual dFlow,
       Assn.list pR r1, Assn.list (pR + J.m) r2,
       Assn.list (pR + 2 * J.m) (rMix r3 (List.replicate J.n 0) a)]⟩)
    with ⟨td1, td2⟩
  · have hle : a ≤ J.n := Nat.le_of_lt hhi
    have hlen := rMix_len hr3_len (List.length_replicate (n := J.n) (a := 0)) hle
    have hb := hdbnd ⟨a, hhi⟩
    have hsm_a : 2 * J.m + J.n + 2 * J.m + a = (J.m + J.m + J.n) + 2 * J.m + a := by omega
    have hd1 : dFlow[2 * J.m + a]'(by omega) = dFlow.getD (2 * J.m + a) 0 :=
      (List.getD_eq_getElem _ _ (by omega)).symm
    have hd2 : dFlow[2 * J.m + J.n + 2 * J.m + a]'(by omega) =
        dFlow.getD ((J.m + J.m + J.n) + 2 * J.m + a) 0 := by
      rw [← List.getD_eq_getElem _ _ (by omega), hsm_a]
    sep_step; sep_step
    rw [hd1] at hdf; rw [hd2] at hdr; subst hdf hdr
    sep_run
    exact rMix_set hr3_len List.length_replicate hhi (by simp [r3])
  rw [rMix_full hr3_len List.length_replicate]
  have hmergeR : Assn.list pR r1 * Assn.list (pR + J.m) r2 * Assn.list (pR + 2 * J.m) r3 =
      Assn.list pR (r1 ++ r2 ++ r3) := by
    rw [Assn.list_append, Assn.list_append, hr1_len, List.length_append, hr1_len, hr2_len,
      show pR + (J.m + J.m) = pR + 2 * J.m by omega]
  have hrout_eq := dualRouting_list_eq J hn_pos fwd rev dFlow (fun v => (hdbnd v).1)
  have hrout_bnds := dualRouting_bounds J hn_pos fwd rev dFlow hdlen hdf_lt hdbnd
  sep_apply hmergeR
  rw [hrout_eq]
  sep_run

end MinCostFlow.NarrowProg.Stage1
