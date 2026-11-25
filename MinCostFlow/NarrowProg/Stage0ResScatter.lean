module

public import MinCostFlow.NarrowProg.Stage0ResLayout
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 5 (Post-Stage-1 scatter): `stage0ResScatterSlice` and `stage0ResScatter`

Scatters Stage 1's optimal residual circulation `g'` from its `K2`-limb buffer into the two
`L`-limb buffers `pHFwd` (forward residual arcs `[0, m2Fwd)`) and `pHRev` (reverse residual arcs
`[m2Fwd, m2)`), and establishes optimality and capacity bounds for `g = R.scatterPositive g'`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### `stage0ResScatterSlice`: scatter a contiguous slice `[startIdx, startIdx + count)` into `pDst` -/

wram_def stage0ResScatterSlice (copyFlow : ℕ)
    (pOrigIdx2, startIdx, count, pFlow2, K2, pDst, L) {
  off := startIdx * K2
  j := startIdx
  for t in 0 .. count {
    d := copyFlow(pFlow2 + off, K2, pDst + mem[pOrigIdx2 + j] * L, L)
    off := off + K2
    j := j + 1
  }
  return 0
}

structure ResScatterSliceData where
  k : ℕ
  m : ℕ
  m2 : ℕ
  startIdx : ℕ
  L : ℕ
  K2 : ℕ
  origIdx : List ℕ
  slice : List (Fin m)
  flowLimbs : Fin m2 → List ℕ
  fval : Fin m → ℕ

def stage0ResScatterSliceSpec (w : ℕ) : Spec ResScatterSliceData where
  pre := fun d args => ⨆ (pOrigIdx2 : ℕ) (pFlow2 : ℕ) (pDst : ℕ),
    ⌜args = [pOrigIdx2, d.startIdx, d.slice.length, pFlow2, d.K2, pDst, d.L] ∧
      1 ≤ d.k ∧ 1 ≤ d.L ∧ d.startIdx + d.slice.length ≤ d.m2 ∧ d.m2 ≤ d.origIdx.length ∧
      d.slice.Nodup ∧
      (∀ t (ht : t < d.slice.length), d.origIdx.getD (d.startIdx + t) 0 = (d.slice[t]'ht).val) ∧
      (∀ j : Fin d.m2, Limbs d.k (d.flowLimbs j) ∧ (d.flowLimbs j).length = d.K2) ∧
      (∀ t (ht : t < d.slice.length) (h2 : d.startIdx + t < d.m2),
        d.fval (d.slice[t]'ht) = Nat.ofDigits (2 ^ d.k) (d.flowLimbs ⟨d.startIdx + t, h2⟩)) ∧
      (∀ e : Fin d.m, e ∉ d.slice → d.fval e = 0) ∧
      (∀ e : Fin d.m, (Nat.digits (2 ^ d.k) (d.fval e)).length ≤ d.L) ∧
      pOrigIdx2 + d.origIdx.length ≤ 2 ^ w ∧ d.origIdx.length < 2 ^ w ∧
      d.m2 * d.K2 < 2 ^ w ∧ pDst + d.m * d.L ≤ 2 ^ w ∧ d.m * d.L < 2 ^ w ∧
      d.K2 < 2 ^ w ∧ d.L < 2 ^ w⌝ *
    Assn.list pOrigIdx2 d.origIdx *
    (∏ j ∈ Finset.range d.m2,
      Assn.list (pFlow2 + j * d.K2) (if h : j < d.m2 then d.flowLimbs ⟨j, h⟩ else [])) *
    (∏ e ∈ Finset.range d.m, Assn.list (pDst + e * d.L) (List.replicate d.L 0))
  post := fun d args v => ⨆ (pOrigIdx2 : ℕ) (pFlow2 : ℕ) (pDst : ℕ),
    ⌜args = [pOrigIdx2, d.startIdx, d.slice.length, pFlow2, d.K2, pDst, d.L] ∧ v = 0⌝ *
    Assn.list pOrigIdx2 d.origIdx *
    (∏ j ∈ Finset.range d.m2,
      Assn.list (pFlow2 + j * d.K2) (if h : j < d.m2 then d.flowLimbs ⟨j, h⟩ else [])) *
    (∏ e ∈ Finset.range d.m,
      Assn.list (pDst + e * d.L)
        (if h : e < d.m then padLimbs (Nat.digits (2 ^ d.k) (d.fval ⟨e, h⟩)) d.L else []))

private theorem resScatterSlice_slot_next (d : ResScatterSliceData) (t : ℕ)
    (ht : t < d.slice.length) (h2 : d.startIdx + t < d.m2)
    (hval : d.fval (d.slice[t]'ht) = Nat.ofDigits (2 ^ d.k) (d.flowLimbs ⟨d.startIdx + t, h2⟩))
    (pDst : ℕ) :
    let e0 := d.slice[t]'ht
    Assn.list (pDst + e0.val * d.L)
      (padLimbs (Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) (d.flowLimbs ⟨d.startIdx + t, h2⟩))) d.L) *
    (∏ e ∈ (Finset.range d.m).erase e0.val,
      Assn.list (pDst + e * d.L)
        (if h : e < d.m then
          if ∃ r : Fin d.slice.length, r.val < t ∧ d.slice[r.val] = ⟨e, h⟩ then
            padLimbs (Nat.digits (2 ^ d.k) (d.fval ⟨e, h⟩)) d.L
          else List.replicate d.L 0
        else [])) =
    (∏ e ∈ Finset.range d.m,
      Assn.list (pDst + e * d.L)
        (if h : e < d.m then
          if ∃ r : Fin d.slice.length, r.val < t + 1 ∧ d.slice[r.val] = ⟨e, h⟩ then
            padLimbs (Nat.digits (2 ^ d.k) (d.fval ⟨e, h⟩)) d.L
          else List.replicate d.L 0
        else [])) := by
  dsimp only
  set e0 := d.slice[t]'ht
  have hmem : e0.val ∈ Finset.range d.m := Finset.mem_range.mpr e0.isLt
  rw [← Finset.mul_prod_erase _ _ hmem]
  congr 1
  · have hex : ∃ r : Fin d.slice.length, r.val < t + 1 ∧ d.slice[r.val] = ⟨e0.val, e0.isLt⟩ :=
      ⟨⟨t, ht⟩, by simp, by simp [e0]⟩
    rw [dite_eq_left e0.isLt, ite_eq_left hex, Fin.eta, hval]
  · refine Finset.prod_congr rfl fun e he => ?_
    have hne : e ≠ e0.val := (Finset.mem_erase.mp he).1
    have hlt : e < d.m := Finset.mem_range.mp (Finset.mem_erase.mp he).2
    rw [dite_eq_left hlt, dite_eq_left hlt]
    have hiff : (∃ r : Fin d.slice.length, r.val < t ∧ d.slice[r.val] = ⟨e, hlt⟩) ↔
        (∃ r : Fin d.slice.length, r.val < t + 1 ∧ d.slice[r.val] = ⟨e, hlt⟩) := by
      constructor
      · rintro ⟨r, hr, heq⟩; exact ⟨r, by omega, heq⟩
      · rintro ⟨r, hr, heq⟩
        by_cases hrt : r.val = t
        · exfalso; apply hne
          have : d.slice[r.val] = e0 := by simp [e0, hrt]
          exact congrArg Fin.val (heq.symm.trans this)
        · exact ⟨r, by omega, heq⟩
    rw [if_congr hiff rfl rfl]

theorem stage0ResScatterSlice_meets {w : ℕ} {p : Program} {f copyFlow : ℕ}
    {Tcf : ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ResScatterSlice copyFlow))
    (hcf : Meets w p copyFlow (copyFlowLimbsSpec.withCost fun x _ =>
      Tcf x.src.length x.dst0.length)) :
    Meets w p f ((stage0ResScatterSliceSpec w).withCost fun d _ =>
      (Tcf d.K2 d.L + 60) * d.slice.length + 40) := by
  sep_enter d with hk1 hL1 hle2 hm2oi hnodup hoiGet hfl hfval hnot hdigLe
    hpOI hoiW hm2K hpDst hmL hKW hLW
  have hstK : d.startIdx * d.K2 < 2 ^ w :=
    lt_of_le_of_lt (Nat.mul_le_mul_right d.K2 (by omega)) hm2K
  have hinit : (∏ e ∈ Finset.range d.m, Assn.list (pDst + e * d.L) (List.replicate d.L 0)) =
      (∏ e ∈ Finset.range d.m,
        Assn.list (pDst + e * d.L)
          (if h : e < d.m then
            if ∃ r : Fin d.slice.length, r.val < 0 ∧ d.slice[r.val] = ⟨e, h⟩ then
              padLimbs (Nat.digits (2 ^ d.k) (d.fval ⟨e, h⟩)) d.L
            else List.replicate d.L 0
          else [])) := by
    refine Finset.prod_congr rfl fun e he => ?_
    rw [dite_eq_left (Finset.mem_range.mp he)]; simp
  sep_apply hinit
  sep_step; sep_step
  sep_for (fun t (d0 : ℕ) => (⟨[pOrigIdx2, d.startIdx, d.slice.length, pFlow2, d.K2, pDst, d.L,
      (d.startIdx + t) * d.K2, d.startIdx + t, t, d0],
      t ≤ d.slice.length,
      (Tcf d.K2 d.L + 45) * (d.slice.length - t) + 15,
      [Assn.list pOrigIdx2 d.origIdx,
       ∏ r ∈ Finset.range d.m2,
         Assn.list (pFlow2 + r * d.K2) (if h : r < d.m2 then d.flowLimbs ⟨r, h⟩ else []),
       ∏ e ∈ Finset.range d.m,
         Assn.list (pDst + e * d.L)
           (if h : e < d.m then
             if ∃ r : Fin d.slice.length, r.val < t ∧ d.slice[r.val] = ⟨e, h⟩ then
               padLimbs (Nat.digits (2 ^ d.k) (d.fval ⟨e, h⟩)) d.L
             else List.replicate d.L 0
           else [])]⟩ : SInv))
    with d0
  · have ht : t < d.slice.length := hhi
    have h2 : d.startIdx + t < d.m2 := by omega
    have h2_mem : d.startIdx + t ∈ Finset.range d.m2 := Finset.mem_range.mpr h2
    set e0 := d.slice[t]'ht
    have he0_mem : e0.val ∈ Finset.range d.m := Finset.mem_range.mpr e0.isLt
    have hget_oi : d.origIdx[d.startIdx + t]'(by omega) = e0.val := by
      have := hoiGet t ht
      rw [List.getD_eq_getElem _ _ (by omega)] at this
      exact this
    have hnot_before : ¬ ∃ r : Fin d.slice.length, r.val < t ∧ d.slice[r.val] = e0 := by
      rintro ⟨r, hr, heq⟩
      have hidx := congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnodup) (a₁ := r) (a₂ := ⟨t, ht⟩) heq)
      dsimp only at hidx; omega
    have hspFl : (∏ r ∈ Finset.range d.m2,
        Assn.list (pFlow2 + r * d.K2) (if h : r < d.m2 then d.flowLimbs ⟨r, h⟩ else [])) =
        Assn.list (pFlow2 + (d.startIdx + t) * d.K2) (d.flowLimbs ⟨d.startIdx + t, h2⟩) *
        (∏ r ∈ (Finset.range d.m2).erase (d.startIdx + t),
          Assn.list (pFlow2 + r * d.K2) (if h : r < d.m2 then d.flowLimbs ⟨r, h⟩ else [])) := by
      rw [← Finset.mul_prod_erase _ _ h2_mem, dite_eq_left h2]
    have hspDst : (∏ e ∈ Finset.range d.m,
        Assn.list (pDst + e * d.L)
          (if h : e < d.m then
            if ∃ r : Fin d.slice.length, r.val < t ∧ d.slice[r.val] = ⟨e, h⟩ then
              padLimbs (Nat.digits (2 ^ d.k) (d.fval ⟨e, h⟩)) d.L
            else List.replicate d.L 0
          else [])) =
        Assn.list (pDst + e0.val * d.L) (List.replicate d.L 0) *
        (∏ e ∈ (Finset.range d.m).erase e0.val,
          Assn.list (pDst + e * d.L)
            (if h : e < d.m then
              if ∃ r : Fin d.slice.length, r.val < t ∧ d.slice[r.val] = ⟨e, h⟩ then
                padLimbs (Nat.digits (2 ^ d.k) (d.fval ⟨e, h⟩)) d.L
              else List.replicate d.L 0
            else [])) := by
      rw [← Finset.mul_prod_erase _ _ he0_mem, dite_eq_left e0.isLt, ite_eq_right hnot_before]
    sep_apply hspFl; sep_apply hspDst
    have he0L_lt : e0.val * d.L < 2 ^ w :=
      lt_of_le_of_lt (Nat.mul_le_mul_right d.L (le_of_lt e0.isLt)) hmL
    have hfl_t := hfl ⟨d.startIdx + t, h2⟩
    have hval_t := hfval t ht h2
    have hdig_t : (Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) (d.flowLimbs ⟨d.startIdx + t, h2⟩))).length ≤
        (List.replicate d.L 0).length := by
      rw [← hval_t, List.length_replicate]; exact hdigLe e0
    have hmul_next : (d.startIdx + t) * d.K2 + d.K2 = (d.startIdx + (t + 1)) * d.K2 := by ring
    have hmul_lt : (d.startIdx + (t + 1)) * d.K2 < 2 ^ w :=
      lt_of_le_of_lt (Nat.mul_le_mul_right d.K2 (by omega)) hm2K
    let cd : CopyFlowLimbsData := ⟨d.k, d.flowLimbs ⟨d.startIdx + t, h2⟩, List.replicate d.L 0⟩
    have hcd_src : cd.src.length = d.K2 := hfl_t.2
    have hcd_dst : cd.dst0.length = d.L := List.length_replicate
    have hcd_lim : Limbs cd.k cd.src := hfl_t.1
    have hdst_atom : Assn.list (pDst + e0.val * d.L) (List.replicate d.L 0) =
        Assn.list (pDst + d.origIdx[d.startIdx + t]'(by omega) * d.L) (List.replicate d.L 0) := by
      rw [hget_oi]
    sep_apply hdst_atom
    sep_step from cd
    · have hdst_back : Assn.list (pDst + d.origIdx[d.startIdx + t]'(by omega) * d.L)
          (padLimbs (Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) (d.flowLimbs ⟨d.startIdx + t, h2⟩)))
            (List.replicate d.L 0).length) =
          Assn.list (pDst + e0.val * d.L)
          (padLimbs (Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) (d.flowLimbs ⟨d.startIdx + t, h2⟩))) d.L) := by
        rw [hget_oi, List.length_replicate]
      sep_apply hdst_back
      sep_apply hspFl.symm
      sep_apply resScatterSlice_slot_next d t ht h2 hval_t pDst
      sep_step; sep_step
      · rw [hcd_src, hcd_dst]; push_cast; ring_nf; omega
    · by_cases hK0 : d.K2 = 0
      · rw [hK0, mul_zero, add_zero]; omega
      · dsimp only [cd] at hcd_src; omega
  · have hfinal : (∏ e ∈ Finset.range d.m,
        Assn.list (pDst + e * d.L)
          (if h : e < d.m then
            if ∃ r : Fin d.slice.length, r.val < d.slice.length ∧ d.slice[r.val] = ⟨e, h⟩ then
              padLimbs (Nat.digits (2 ^ d.k) (d.fval ⟨e, h⟩)) d.L
            else List.replicate d.L 0
          else [])) =
        (∏ e ∈ Finset.range d.m,
          Assn.list (pDst + e * d.L)
            (if h : e < d.m then padLimbs (Nat.digits (2 ^ d.k) (d.fval ⟨e, h⟩)) d.L else [])) := by
      refine Finset.prod_congr rfl fun e he => ?_
      have hlt := Finset.mem_range.mp he
      rw [dite_eq_left hlt, dite_eq_left hlt]
      by_cases hmem : (⟨e, hlt⟩ : Fin d.m) ∈ d.slice
      · obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hmem
        rw [ite_eq_left ⟨⟨idx, hidx⟩, hidx, hget⟩]
      · have hno : ¬ ∃ r : Fin d.slice.length, r.val < d.slice.length ∧ d.slice[r.val] = ⟨e, hlt⟩ := by
          rintro ⟨r, _, heq⟩; exact hmem (heq ▸ List.getElem_mem r.isLt)
        rw [ite_eq_right hno, hnot ⟨e, hlt⟩ hmem]
        simp [padLimbs]
    sep_apply hfinal
    sep_step

/-! ### `stage0ResScatter`: scatter both forward and reverse residual flows -/

wram_def stage0ResScatter (slice : ℕ)
    (m2Fwd, m2, pOrigIdx2, pOut2, pHFwd, pHRev, L) {
  pFlow2 := mem[pOut2]
  K2 := mem[pOut2 + 1]
  d := slice(pOrigIdx2, 0, m2Fwd, pFlow2, K2, pHFwd, L)
  d := slice(pOrigIdx2, m2Fwd, m2 - m2Fwd, pFlow2, K2, pHRev, L)
  return 0
}

structure ResScatterData where
  I : Instance
  hv : I.IsValid
  f : Fin I.m → ℤ
  hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)
  L : ℕ
  g' : Fin ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m → ℤ
  flowLimbs : Fin ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m → List ℕ

def stage0ResScatterSpec (w : ℕ) : Spec ResScatterData where
  pre := fun d args => ⨆ (pOrigIdx2 : ℕ) (pOut2 : ℕ) (pHFwd : ℕ) (pHRev : ℕ) (pFlow2 : ℕ),
    let R := (FlowReduction.shiftedGraph d.I d.hv).residual d.f
    let R' := R.withoutZeroEdges
    let fwd := resFwdPos d.I d.hv d.f d.I.m
    let rev := resRevPos d.I d.f d.I.m
    let k := narrowLimbWidth d.I
    let K2 := bitScalingPhases R' / k + 2
    ⌜args = [fwd.length, R'.m, pOrigIdx2, pOut2, pHFwd, pHRev, d.L] ∧
      1 ≤ d.L ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length ≤ d.L) ∧
      R'.Optimal (fun j => (d.g' j : ℝ)) ∧
      (∀ j : Fin R'.m, 0 ≤ d.g' j ∧ Limbs k (d.flowLimbs j) ∧ (d.flowLimbs j).length = K2 ∧
        ((Nat.ofDigits (2 ^ k) (d.flowLimbs j) : ℕ) : ℤ) = d.g' j) ∧
      pOrigIdx2 + 2 * d.I.m ≤ 2 ^ w ∧ 2 * d.I.m < 2 ^ w ∧ pOut2 + 2 ≤ 2 ^ w ∧
      R'.m * K2 < 2 ^ w ∧
      pHFwd + d.I.m * d.L ≤ 2 ^ w ∧ pHRev + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      K2 < 2 ^ w ∧ d.L < 2 ^ w⌝ *
    Assn.list pOrigIdx2 ((fwd.map Fin.val ++ rev.map Fin.val) ++ List.replicate (2 * d.I.m - R'.m) 0) *
    Assn.list pOut2 [pFlow2, K2] *
    (∏ j ∈ Finset.range R'.m,
      Assn.list (pFlow2 + j * K2) (if h : j < R'.m then d.flowLimbs ⟨j, h⟩ else [])) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pHFwd + e * d.L) (List.replicate d.L 0)) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pHRev + e * d.L) (List.replicate d.L 0))
  post := fun d args v => ⨆ (pOrigIdx2 : ℕ) (pOut2 : ℕ) (pHFwd : ℕ) (pHRev : ℕ),
    let R := (FlowReduction.shiftedGraph d.I d.hv).residual d.f
    let R' := R.withoutZeroEdges
    let fwd := resFwdPos d.I d.hv d.f d.I.m
    let k := narrowLimbWidth d.I
    let g := R.scatterPositive d.g'
    ⌜args = [fwd.length, R'.m, pOrigIdx2, pOut2, pHFwd, pHRev, d.L] ∧ v = 0 ∧
      R.Optimal (fun a => (g a : ℝ)) ∧
      (∀ e : Fin d.I.m, 0 ≤ g (Fin.castAdd d.I.m e) ∧ 0 ≤ g (Fin.natAdd d.I.m e)) ∧
      (∀ e : Fin d.I.m, (g (Fin.natAdd d.I.m e)).toNat ≤ (d.f e).toNat) ∧
      (∀ e : Fin d.I.m, (d.f e).toNat + (g (Fin.castAdd d.I.m e)).toNat ≤
        (FlowReduction.shiftedGraph d.I d.hv).capacity e)⌝ *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pHFwd + e * d.L)
        (if h : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (g (Fin.castAdd d.I.m ⟨e, h⟩)).toNat) d.L else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pHRev + e * d.L)
        (if h : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (g (Fin.natAdd d.I.m ⟨e, h⟩)).toNat) d.L else [])) *
    Assn.gc

theorem stage0ResScatter_meets {w : ℕ} {p : Program} {f slice : ℕ}
    {Tsl : ℕ → ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ResScatter slice))
    (hsl : Meets w p slice ((stage0ResScatterSliceSpec w).withCost fun x _ =>
      Tsl x.K2 x.L x.slice.length)) :
    Meets w p f ((stage0ResScatterSpec w).withCost fun d _ =>
      let R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
      let K2 := bitScalingPhases R' / narrowLimbWidth d.I + 2
      Tsl K2 d.L (resFwdPos d.I d.hv d.f d.I.m).length +
      Tsl K2 d.L (resRevPos d.I d.f d.I.m).length + 100) := by
  sep_enter d with hL1 hcapDig hopt' hfl hpOI h2mW hpOut2 hm2K hpHF hpHR hmL hKW hLW
  set R := (FlowReduction.shiftedGraph d.I d.hv).residual d.f
  set R' := R.withoutZeroEdges
  set fwd := resFwdPos d.I d.hv d.f d.I.m
  set rev := resRevPos d.I d.f d.I.m
  set k := narrowLimbWidth d.I
  set K2 := bitScalingPhases R' / k + 2
  set g := R.scatterPositive d.g'
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have hb2k : 1 < 2 ^ k := by have := two_le_pow hk1; omega
  have hm_eq : R'.m = fwd.length + rev.length := res_m_eq d.I d.hv d.f
  have hm_le : R'.m ≤ 2 * d.I.m := res_m_le_two_m d.I d.hv d.f
  have hopt_g : R.Optimal (fun a => (g a : ℝ)) := by
    have h1 := R.extendPositive_optimal (fun j => (d.g' j : ℝ)) hopt'
    have h2 : (fun a => (g a : ℝ)) = R.extendPositive (fun j => (d.g' j : ℝ)) := by
      ext a
      rw [congrFun (R.scatterPositive_cast d.g') a,
          congrFun (R.scatterPositive_eq_extendPositive (fun j => (d.g' j : ℝ))) a]
    rwa [h2]
  have hg_bounds : ∀ a : Fin R.m, 0 ≤ g a ∧ g a ≤ (R.capacity a : ℤ) := fun a => by
    have hfeas := hopt_g.1.2 a
    have h1 : (0 : ℝ) ≤ (g a : ℝ) := hfeas.1
    have h2 : (g a : ℝ) ≤ ((R.capacity a : ℤ) : ℝ) := by simpa using hfeas.2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hg_nn : ∀ e : Fin d.I.m, 0 ≤ g (Fin.castAdd d.I.m e) ∧ 0 ≤ g (Fin.natAdd d.I.m e) :=
    fun e => ⟨(hg_bounds _).1, (hg_bounds _).1⟩
  have hg_rev_le : ∀ e : Fin d.I.m, (g (Fin.natAdd d.I.m e)).toNat ≤ (d.f e).toNat := fun e => by
    have h1 := (hg_bounds (Fin.natAdd d.I.m e)).2
    have h2 : R.capacity (Fin.natAdd d.I.m e) = (d.f e).toNat := by simp only [R, Fin.addCases_right]
    rw [h2] at h1
    have hnn := (hg_nn e).2
    omega
  have hg_fwd_le : ∀ e : Fin d.I.m, (d.f e).toNat + (g (Fin.castAdd d.I.m e)).toNat ≤
      (FlowReduction.shiftedGraph d.I d.hv).capacity e := fun e => by
    have h1 := (hg_bounds (Fin.castAdd d.I.m e)).2
    have h2 : R.capacity (Fin.castAdd d.I.m e) =
        (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat := by
      simp only [R, Fin.addCases_left]
    rw [h2] at h1
    have ⟨hf0, hfcap⟩ := d.hf e
    have hnn := (hg_nn e).1
    omega
  have hdig_fwd : ∀ e : Fin d.I.m, (Nat.digits (2 ^ k) (g (Fin.castAdd d.I.m e)).toNat).length ≤ d.L := fun e => by
    have h1 : (g (Fin.castAdd d.I.m e)).toNat ≤ (FlowReduction.shiftedGraph d.I d.hv).capacity e := by
      have := hg_fwd_le e; omega
    exact le_trans (digits_length_mono hb2k h1) (hcapDig e)
  have hdig_rev : ∀ e : Fin d.I.m, (Nat.digits (2 ^ k) (g (Fin.natAdd d.I.m e)).toNat).length ≤ d.L := fun e => by
    have ⟨hf0, hfcap⟩ := d.hf e
    have h1 : (g (Fin.natAdd d.I.m e)).toNat ≤ (FlowReduction.shiftedGraph d.I d.hv).capacity e := by
      have := hg_rev_le e; omega
    exact le_trans (digits_length_mono hb2k h1) (hcapDig e)
  set oiList := (fwd.map Fin.val ++ rev.map Fin.val) ++ List.replicate (2 * d.I.m - R'.m) 0
  have hoi_len : oiList.length = 2 * d.I.m := by
    simp only [oiList, List.length_append, List.length_map, List.length_replicate]; omega
  have hm_pe : ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).positiveEdges.length =
      fwd.length + rev.length := hm_eq
  have hm_pe_le : ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).positiveEdges.length ≤ oiList.length := by
    rw [hoi_len]; exact hm_le
  have hpOI' : pOrigIdx2 + oiList.length ≤ 2 ^ w := by rw [hoi_len]; exact hpOI
  have hoiW' : oiList.length < 2 ^ w := by rw [hoi_len]; exact h2mW
  sep_apply (list_join_two pOut2 pFlow2 K2).symm
  sep_step; sep_step
  -- Call 1: scatter forward slice [0, fwd.length) into pHFwd
  let sd1 : ResScatterSliceData := ⟨k, d.I.m, R'.m, 0, d.L, K2, oiList, fwd, d.flowLimbs,
    fun e => (g (Fin.castAdd d.I.m e)).toNat⟩
  have hsd1_nodup : sd1.slice.Nodup := resFwdPos_nodup d.I d.hv d.f d.I.m
  have hsd1_oi : ∀ t (ht : t < sd1.slice.length),
      sd1.origIdx.getD (sd1.startIdx + t) 0 = (sd1.slice[t]'ht).val := by
    intro t ht
    dsimp only [sd1] at ht ⊢
    rw [List.getD_eq_getElem _ _ (by rw [hoi_len]; omega)]
    simp only [oiList]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; exact ht),
        List.getElem_map]
    simp
  have hsd1_fl : ∀ j : Fin sd1.m2, Limbs sd1.k (sd1.flowLimbs j) ∧ (sd1.flowLimbs j).length = sd1.K2 :=
    fun j => ⟨(hfl j).2.1, (hfl j).2.2.1⟩
  have hsd1_val : ∀ t (ht : t < sd1.slice.length) (h2 : sd1.startIdx + t < sd1.m2),
      sd1.fval (sd1.slice[t]'ht) = Nat.ofDigits (2 ^ sd1.k) (sd1.flowLimbs ⟨sd1.startIdx + t, h2⟩) := by
    intro t ht h2
    dsimp only [sd1] at ht h2 ⊢
    have h2' : t < R'.m := by omega
    have hs := res_scatterPositive_fwd d.I d.hv d.f d.g' t ht
    dsimp only at hs
    have hof := (hfl ⟨t, h2'⟩).2.2.2
    change (g (Fin.castAdd d.I.m (fwd[t]'ht))).toNat = Nat.ofDigits (2 ^ k) (d.flowLimbs ⟨0 + t, h2⟩)
    rw [show g = R.scatterPositive d.g' from rfl, hs]
    have hidx : (⟨0 + t, h2⟩ : Fin R'.m) = ⟨t, h2'⟩ := Fin.ext (Nat.zero_add t)
    rw [hidx, ← hof]; exact Int.toNat_natCast _
  have hsd1_not : ∀ e : Fin sd1.m, e ∉ sd1.slice → sd1.fval e = 0 := by
    intro e hne
    have hz := res_scatterPositive_not_fwd d.I d.hv d.f d.g' e hne
    change (g (Fin.castAdd d.I.m e)).toNat = 0
    rw [show g = R.scatterPositive d.g' from rfl, hz]; rfl
  have hsd1_dig : ∀ e : Fin sd1.m, (Nat.digits (2 ^ sd1.k) (sd1.fval e)).length ≤ sd1.L := hdig_fwd
  sep_step from sd1
  · -- Call 2: scatter reverse slice [fwd.length, fwd.length + rev.length) into pHRev
    let sd2 : ResScatterSliceData := ⟨k, d.I.m, R'.m, fwd.length, d.L, K2, oiList, rev, d.flowLimbs,
      fun e => (g (Fin.natAdd d.I.m e)).toNat⟩
    have hsd2_nodup : sd2.slice.Nodup := resRevPos_nodup d.I d.f d.I.m
    have hsd2_oi : ∀ t (ht : t < sd2.slice.length),
        sd2.origIdx.getD (sd2.startIdx + t) 0 = (sd2.slice[t]'ht).val := by
      intro t ht
      dsimp only [sd2] at ht ⊢
      rw [List.getD_eq_getElem _ _ (by rw [hoi_len]; omega)]
      simp only [oiList]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp),
          List.getElem_map]
      simp [rev]
    have hsd2_fl : ∀ j : Fin sd2.m2, Limbs sd2.k (sd2.flowLimbs j) ∧ (sd2.flowLimbs j).length = sd2.K2 :=
      fun j => ⟨(hfl j).2.1, (hfl j).2.2.1⟩
    have hsd2_val : ∀ t (ht : t < sd2.slice.length) (h2 : sd2.startIdx + t < sd2.m2),
        sd2.fval (sd2.slice[t]'ht) = Nat.ofDigits (2 ^ sd2.k) (sd2.flowLimbs ⟨sd2.startIdx + t, h2⟩) := by
      intro t ht h2
      dsimp only [sd2] at ht h2 ⊢
      have hs := res_scatterPositive_rev d.I d.hv d.f d.g' t ht
      dsimp only at hs
      have hof := (hfl ⟨fwd.length + t, h2⟩).2.2.2
      change (g (Fin.natAdd d.I.m (rev[t]'ht))).toNat = Nat.ofDigits (2 ^ k) (d.flowLimbs ⟨fwd.length + t, h2⟩)
      rw [show g = R.scatterPositive d.g' from rfl, hs, ← hof]
      exact Int.toNat_natCast _
    have hsd2_not : ∀ e : Fin sd2.m, e ∉ sd2.slice → sd2.fval e = 0 := by
      intro e hne
      have hz := res_scatterPositive_not_rev d.I d.hv d.f d.g' e hne
      change (g (Fin.natAdd d.I.m e)).toNat = 0
      rw [show g = R.scatterPositive d.g' from rfl, hz]; rfl
    have hsd2_dig : ∀ e : Fin sd2.m, (Nat.digits (2 ^ sd2.k) (sd2.fval e)).length ≤ sd2.L := hdig_rev
    sep_step from sd2
    · sep_apply (Assn.noDebt_prod (Finset.range R'.m) fun j _ =>
        Assn.noDebt_list (pFlow2 + j * K2) (if h : j < R'.m then d.flowLimbs ⟨j, h⟩ else [])).le_gc
      sep_step
      · dsimp only [sd1, sd2]; omega
    · simp only [sd2]; omega
    · simp only [sd2]; omega
  · simp only [sd1]; omega

end MinCostFlow.NarrowProg
