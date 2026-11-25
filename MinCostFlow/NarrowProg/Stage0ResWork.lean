module

public import MinCostFlow.NarrowProg.Stage0ResRev
public import MinCostFlow.NarrowProg.Stage0ResScatter
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 5 (worker): `stage0ResSpace`, `split_free_res`, `stage0ResRun`, and `stage0ResWork`

Allocates the exact `stage0ResSpace m L totCost = 16 * m + 3 * m * L + 2 * totCost + 12` words,
builds `R' = ((shiftedGraph I hv).residual f).withoutZeroEdges`, splits `pCapBuf2 * pFeasFlow` into
the capacity-limb product of `stage1Input R'` via `res_split_capBuf_feasFlow`, calls `stage1Circ`
and `resScatter` via `stage0ResRun`, restores `pFeasFlow` intact via `hcap_split.symm`, and returns
the optimal residual circulation `g = R.scatterPositive g'` scattered into `pHFwd` and `pHRev`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow
open MinCostFlow.NarrowProg.Stage1

namespace MinCostFlow.NarrowProg

/-! ### Space budget and heap split -/

/-- Exact heap space allocated by `stage0Res` before calling `stage1Circ`:
`10 + 2 + 8 * (2 * m) + m * L + 2 * totCost + 2 * m * L = 16 * m + 3 * m * L + 2 * totCost + 12`. -/
def stage0ResSpace (m L totCost : ℕ) : ℕ :=
  10 + 2 + 8 * (2 * m) + m * L + 2 * totCost + 2 * m * L

theorem stage0ResSpace_eq (m L totCost : ℕ) :
    stage0ResSpace m L totCost = 16 * m + 3 * m * L + 2 * totCost + 12 := by
  unfold stage0ResSpace; ring

theorem totCostLimbs_le_mul_max (I : Instance) :
    totCostLimbs I ≤ I.m * narrowMaxCostLimbs I := by
  unfold totCostLimbs
  have hk1 : 1 ≤ narrowLimbWidth I := one_le_narrowLimbWidth I
  have hb : 1 < 2 ^ narrowLimbWidth I := by have := two_le_pow hk1; omega
  calc ∑ e : Fin I.m, (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).cost.natAbs).length
      ≤ ∑ _e : Fin I.m, narrowMaxCostLimbs I := by
        refine Finset.sum_le_sum fun e _ => digits_length_mono hb (cost_natAbs_le_maxCost' I e)
    _ = I.m * narrowMaxCostLimbs I := by simp

theorem split_free_res {h m L totCost w : ℕ}
    (hfit : h + stage0ResSpace m L totCost < 2 ^ w) :
    let cap := 2 * m
    let bufCap := 2 * totCost
    Assn.free h (2 ^ w - h) ≤
      Assn.list h (List.replicate 10 0) *
      Assn.list (h + 10) (List.replicate 2 0) *
      Assn.list (h + 10 + 2) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap + cap + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap + cap) (List.replicate cap 0) *
      Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap) (List.replicate cap 0) *
      (∏ e ∈ Finset.range m,
        Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + e * L)
          (List.replicate L 0)) *
      Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L)
        (List.replicate bufCap 0) *
      (∏ e ∈ Finset.range m,
        Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L + bufCap + e * L)
          (List.replicate L 0)) *
      (∏ e ∈ Finset.range m,
        Assn.list (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L + bufCap + m * L + e * L)
          (List.replicate L 0)) *
      Assn.free (h + stage0ResSpace m L totCost) (2 ^ w - (h + stage0ResSpace m L totCost)) := by
  dsimp only
  set cap := 2 * m
  set bufCap := 2 * totCost
  have hsp : h + stage0ResSpace m L totCost =
      h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L + bufCap + m * L + m * L := by
    unfold stage0ResSpace; ring
  rw [hsp]
  have hfit' : h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L + bufCap + m * L + m * L < 2 ^ w :=
    hsp ▸ hfit
  rw [show 2 ^ w - h = 10 + (2 ^ w - (h + 10)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10) = 2 + (2 ^ w - (h + 10 + 2)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2) = cap + (2 ^ w - (h + 10 + 2 + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap) = cap + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap) = m * L + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L)) by omega, Assn.free_add',
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L) = bufCap + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L + bufCap)) by omega, Assn.free_add,
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L + bufCap) = m * L + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L + bufCap + m * L)) by omega, Assn.free_add',
      show 2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L + bufCap + m * L) = m * L + (2 ^ w - (h + 10 + 2 + cap + cap + cap + cap + cap + cap + cap + cap + m * L + bufCap + m * L + m * L)) by omega, Assn.free_add',
      free_to_prod_replicate, free_to_prod_replicate, free_to_prod_replicate]
  simp only [← mul_assoc]
  exact le_refl _

/-! ### Pure arithmetic helper for Stage 1 on `R'` -/

private theorem resWork_stage1_arith {w : ℕ} {S : ℕ → ℕ → ℕ}
    (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
    {L h : ℕ} (hLge : narrowMaxCapLimbs I + 1 ≤ L) (hLlt : L < 2 ^ narrowLimbWidth I)
    (h2k1 : 2 * narrowLimbWidth I + 1 ≤ w)
    (hclip : (18 * I.m + 21) * upperClip (3 * I.m) < 2 ^ w)
    (hfit1 : h + stage1CircSpace ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
      (narrowLimbWidth I) S < 2 ^ w) :
    let k := narrowLimbWidth I
    let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    let K2 := bitScalingPhases R' / k + 2
    2 * R'.m + 1 < 2 ^ k ∧
    (6 * R'.m + 21) * upperClip R'.m < 2 ^ w ∧
    6 * R'.m + 4 < 2 ^ w ∧
    k + Nat.log 2 (2 * k) + 2 ≤ w ∧
    K2 ≤ L + 2 ∧
    R'.m * K2 < 2 ^ w ∧
    K2 < 2 ^ w := by
  dsimp only
  set k := narrowLimbWidth I
  set R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
  set K2 := bitScalingPhases R' / k + 2
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth I
  have hm_le : R'.m ≤ 2 * I.m := res_m_le_two_m I hv f
  have h2U_le_bud : 2 * I.maxCapacity ≤ FlowReduction.scalingCapacityBudget I I.maxCapacity := by
    unfold FlowReduction.scalingCapacityBudget
    have : 2 * (I.m + 1) * I.maxCapacity = 2 * I.m * I.maxCapacity + 2 * I.maxCapacity := by ring
    omega
  have h2m1_lt : 2 * R'.m + 1 < 2 ^ k := by
    have h6m : 6 * I.m + 1 < 2 ^ k := six_mul_m_add_one_lt_pow_limbWidth I hv
    omega
  have hclip_R' : (6 * R'.m + 21) * upperClip R'.m < 2 ^ w := by
    have h1 : (6 * R'.m + 21) * upperClip R'.m ≤ (18 * I.m + 21) * upperClip (3 * I.m) :=
      Nat.mul_le_mul (by omega) (upperClip_mono (by omega))
    omega
  have h6m4_lt : 6 * R'.m + 4 < 2 ^ w := by
    have h1 := upperClip_pos R'.m
    have h2 : 6 * R'.m + 4 ≤ (6 * R'.m + 21) * upperClip R'.m :=
      calc 6 * R'.m + 4 ≤ (6 * R'.m + 21) * 1 := by omega
        _ ≤ (6 * R'.m + 21) * upperClip R'.m := Nat.mul_le_mul_left _ h1
    omega
  have hK2_le : K2 ≤ L + 2 := by
    have h1 := stage1_Kcap_le_maxCapLimbs I hv R'
      (le_trans (residual_withoutZeroEdges_maxCapacity_le I hv f hf) h2U_le_bud)
    dsimp only [K2, k]; omega
  have hFlow_lt : R'.m * K2 < 2 ^ w := by
    by_cases hm0 : R'.m = 0
    · rw [hm0, zero_mul]; exact Nat.pow_pos (by decide)
    · have hsp : 5 * R'.m * K2 ≤ stage1CircSpace R' k S := by
        unfold stage1CircSpace stage1StartSpace
        rw [ite_eq_right hm0]
        dsimp only [K2, k]
        omega
      have hle : R'.m * K2 ≤ 5 * R'.m * K2 := Nat.mul_le_mul_right K2 (by omega)
      omega
  have hK2W : K2 < 2 ^ w := by
    have hpow : 2 ^ k + 2 ≤ 2 ^ w := by
      have h1 : 2 ^ (k + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk3
      rw [Nat.pow_succ] at h1; omega
    omega
  exact ⟨h2m1_lt, hclip_R', h6m4_lt, stage1_k_log_bound hk3 h2k1, hK2_le, hFlow_lt, hK2W⟩

/-! ### `stage0ResRun`: invoke `stage1Circ` then `resScatter` -/

wram_def stage0ResRun (stage1Circ resScatter : ℕ)
    (pIn2, pOut2, pOrigIdx2, pHFwd, pHRev, m2Fwd, m2, L, h) {
  h1 := stage1Circ(pIn2, pOut2, h)
  d := resScatter(m2Fwd, m2, pOrigIdx2, pOut2, pHFwd, pHRev, L)
  return h1
}

structure Stage0ResRunData where
  I : Instance
  hv : I.IsValid
  f : Fin I.m → ℤ
  hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)
  L : ℕ
  hLge : narrowMaxCapLimbs I + 1 ≤ L
  pCapBuf2 : ℕ
  pFeasFlow : ℕ
  pCostBuf2 : ℕ

def stage0ResRunSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Stage0ResRunData where
  pre := fun d args => ⨆ (pIn2 : ℕ) (pOut2 : ℕ) (pOrigIdx2 : ℕ) (pHFwd : ℕ) (pHRev : ℕ) (h : ℕ)
      (pTail : ℕ) (pHead : ℕ) (pCapPtrs : ℕ) (pCapLens : ℕ)
      (pCostSign : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ),
    let k := narrowLimbWidth d.I
    let R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
    let fwd := resFwdPos d.I d.hv d.f d.I.m
    let rev := resRevPos d.I d.f d.I.m
    ⌜args = [pIn2, pOut2, pOrigIdx2, pHFwd, pHRev, fwd.length, R'.m, d.L, h] ∧
      d.L < 2 ^ k ∧ 2 * k + 1 ≤ w ∧ (18 * d.I.m + 21) * upperClip (3 * d.I.m) < 2 ^ w ∧
      d.I.m * d.L < 2 ^ w ∧ pOut2 + 2 ≤ 2 ^ w ∧
      pOrigIdx2 + 2 * d.I.m ≤ 2 ^ w ∧ 2 * d.I.m < 2 ^ w ∧
      pHFwd + d.I.m * d.L ≤ 2 ^ w ∧ pHRev + d.I.m * d.L ≤ 2 ^ w ∧
      d.I.n + 1 < 2 ^ w ∧ h + stage1CircSpace R' k S < 2 ^ w ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length ≤ d.L) ∧
      (∀ j (hj : j < R'.m),
        CanonicalLimbs k ((resCapLimbs d.I d.hv d.f).getD j []) ∧
        ((resCapLimbs d.I d.hv d.f).getD j []).length * k < 2 ^ w ∧
        Nat.ofDigits (2 ^ k) ((resCapLimbs d.I d.hv d.f).getD j []) = R'.capacity ⟨j, hj⟩) ∧
      (∀ j (hj : j < R'.m),
        CanonicalLimbs k ((resCostLimbs d.I d.hv d.f).getD j []) ∧
        ((resCostLimbs d.I d.hv d.f).getD j []).length * k < 2 ^ w ∧
        Nat.ofDigits (2 ^ k) ((resCostLimbs d.I d.hv d.f).getD j []) = (R'.cost ⟨j, hj⟩).natAbs)⌝ *
    stage1Input R' k (resCapPtrs d.I d.hv d.f d.pCapBuf2 d.pFeasFlow d.L) (resCapLimbs d.I d.hv d.f)
      (resCostPtrs d.I d.hv d.f d.pCostBuf2) (resCostLimbs d.I d.hv d.f)
      pIn2 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens *
    Assn.list pOut2 [R'.m, 0] *
    Assn.list pOrigIdx2 ((fwd.map Fin.val ++ rev.map Fin.val) ++ List.replicate (2 * d.I.m - R'.m) 0) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pHFwd + e * d.L) (List.replicate d.L 0)) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pHRev + e * d.L) (List.replicate d.L 0)) *
    Assn.free h (2 ^ w - h)
  post := fun d args h' => ⨆ (pIn2 : ℕ) (pOut2 : ℕ) (pOrigIdx2 : ℕ) (pHFwd : ℕ) (pHRev : ℕ) (h : ℕ)
      (pTail : ℕ) (pHead : ℕ) (pCapPtrs : ℕ) (pCapLens : ℕ)
      (pCostSign : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ)
      (g : Fin (d.I.m + d.I.m) → ℤ),
    let k := narrowLimbWidth d.I
    let R := (FlowReduction.shiftedGraph d.I d.hv).residual d.f
    let R' := R.withoutZeroEdges
    let fwd := resFwdPos d.I d.hv d.f d.I.m
    ⌜args = [pIn2, pOut2, pOrigIdx2, pHFwd, pHRev, fwd.length, R'.m, d.L, h] ∧
      h ≤ h' ∧ h' ≤ h + stage1CircSpace R' k S ∧
      R.Optimal (fun a => (g a : ℝ)) ∧
      (∀ e : Fin d.I.m, 0 ≤ g (Fin.castAdd d.I.m e) ∧ 0 ≤ g (Fin.natAdd d.I.m e)) ∧
      (∀ e : Fin d.I.m, (g (Fin.natAdd d.I.m e)).toNat ≤ (d.f e).toNat) ∧
      (∀ e : Fin d.I.m, (d.f e).toNat + (g (Fin.castAdd d.I.m e)).toNat ≤
        (FlowReduction.shiftedGraph d.I d.hv).capacity e)⌝ *
    stage1Input R' k (resCapPtrs d.I d.hv d.f d.pCapBuf2 d.pFeasFlow d.L) (resCapLimbs d.I d.hv d.f)
      (resCostPtrs d.I d.hv d.f d.pCostBuf2) (resCostLimbs d.I d.hv d.f)
      pIn2 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pHFwd + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (g (Fin.castAdd d.I.m ⟨e, hlt⟩)).toNat) d.L else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pHRev + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (g (Fin.natAdd d.I.m ⟨e, hlt⟩)).toNat) d.L else [])) *
    Assn.free h' (2 ^ w - h') * Assn.gc

theorem stage0ResRun_meets {w : ℕ} {p : Program} {S : ℕ → ℕ → ℕ}
    {f stage1Circ resScatter : ℕ}
    {T1 : Circulation → ℕ} {Tsc : ℕ → ℕ → ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ResRun stage1Circ resScatter))
    (hs1 : Meets w p stage1Circ ((stage1CircSpec w S).withCost fun x _ => T1 x.1))
    (hsc : Meets w p resScatter ((stage0ResScatterSpec w).withCost fun d _ =>
      let R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
      let K2 := bitScalingPhases R' / narrowLimbWidth d.I + 2
      Tsc K2 d.L (resFwdPos d.I d.hv d.f d.I.m).length (resRevPos d.I d.f d.I.m).length)) :
    Meets w p f ((stage0ResRunSpec w S).withCost fun d _ =>
      let R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
      let K2 := bitScalingPhases R' / narrowLimbWidth d.I + 2
      T1 R' + Tsc K2 d.L (resFwdPos d.I d.hv d.f d.I.m).length (resRevPos d.I d.f d.I.m).length + 70) := by
  sep_enter d with hLlt h2k1 hclip hmL hpOut2 hpOI hcapW hpHF hpHR hn1W hfit1 hshCapLen hcapSpec hcostSpec
  set k := narrowLimbWidth d.I
  set R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have hLge : narrowMaxCapLimbs d.I + 1 ≤ d.L := d.hLge
  have hL1 : 1 ≤ d.L := by omega
  have hLW : d.L < 2 ^ w :=
    lt_of_lt_of_le hLlt (Nat.pow_le_pow_right (by decide) (by omega : k ≤ w))
  obtain ⟨h2m1_lt, hclip_R', h6m4_lt, hklg, _, hFlow_lt, hK2W⟩ :=
    resWork_stage1_arith d.I d.hv d.f d.hf d.hLge hLlt h2k1 hclip hfit1
  have hcpLen := resCapPtrs_length d.I d.hv d.f d.pCapBuf2 d.pFeasFlow d.L
  have hclLen := resCapLimbs_length d.I d.hv d.f
  have hcopLen := resCostPtrs_length d.I d.hv d.f d.pCostBuf2
  have hcolLen := resCostLimbs_length d.I d.hv d.f
  sep_step from (R', k, resCapPtrs d.I d.hv d.f d.pCapBuf2 d.pFeasFlow d.L, resCapLimbs d.I d.hv d.f,
      resCostPtrs d.I d.hv d.f d.pCostBuf2, resCostLimbs d.I d.hv d.f, [R'.m, 0])
    with hh1_lo hh1_hi hopt_R' hfl_R'
  sep_step from (⟨d.I, d.hv, d.f, d.hf, d.L, f_1, flowLimbs⟩ : ResScatterData)
    with hopt_g hg_nn hg_rev hg_fwd
  sep_step
  · dsimp only [R', k]; omega

/-! ### `stage0ResWork`: build → `stage0ResRun` → restore `pFeasFlow` -/

wram_def stage0ResWork (resBuild resRun : ℕ)
    (pEdges, pShCapBuf, pFeasFlow, n, m, L, k,
     pIn2, pOut2, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2,
     pOrigIdx2, pCapBuf2, pCostBuf2, pHFwd, pHRev, h) {
  m2Fwd := resBuild(pEdges, m, n, k, pShCapBuf, pFeasFlow, pCapBuf2, pCostBuf2, L,
    pIn2, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pOut2)
  m2 := mem[pOut2]
  h1 := resRun(pIn2, pOut2, pOrigIdx2, pHFwd, pHRev, m2Fwd, m2, L, h)
  return h1
}

structure Stage0ResWorkData where
  I : Instance
  hv : I.IsValid
  f : Fin I.m → ℤ
  hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)
  L : ℕ
  hLge : narrowMaxCapLimbs I + 1 ≤ L

def stage0ResWorkSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Stage0ResWorkData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ)
      (pIn2 : ℕ) (pOut2 : ℕ) (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ)
      (pCapBuf2 : ℕ) (pCostBuf2 : ℕ) (pHFwd : ℕ) (pHRev : ℕ) (h : ℕ),
    let k := narrowLimbWidth d.I
    let R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
    let cap := 2 * d.I.m
    let bufCap := 2 * totCostLimbs d.I
    ⌜args = [pEdges, pShCapBuf, pFeasFlow, d.I.n, d.I.m, d.L, k,
        pIn2, pOut2, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2,
        pOrigIdx2, pCapBuf2, pCostBuf2, pHFwd, pHRev, h] ∧
      d.L < 2 ^ k ∧ 2 * k + 1 ≤ w ∧ (18 * d.I.m + 21) * upperClip (3 * d.I.m) < 2 ^ w ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pIn2 + 10 ≤ 2 ^ w ∧ pOut2 + 2 ≤ 2 ^ w ∧
      pTail2 + cap ≤ 2 ^ w ∧ pHead2 + cap ≤ 2 ^ w ∧
      pCapPtr2 + cap ≤ 2 ^ w ∧ pCapLen2 + cap ≤ 2 ^ w ∧
      pCostSign2 + cap ≤ 2 ^ w ∧ pCostPtr2 + cap ≤ 2 ^ w ∧
      pCostLen2 + cap ≤ 2 ^ w ∧ pOrigIdx2 + cap ≤ 2 ^ w ∧ cap < 2 ^ w ∧
      pCapBuf2 + d.I.m * d.L ≤ 2 ^ w ∧ pCostBuf2 + bufCap < 2 ^ w ∧ bufCap < 2 ^ w ∧
      pHFwd + d.I.m * d.L ≤ 2 ^ w ∧ pHRev + d.I.m * d.L ≤ 2 ^ w ∧
      d.I.n + 1 < 2 ^ w ∧ h + stage1CircSpace R' k S < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    Assn.list pIn2 (List.replicate 10 0) *
    Assn.list pOut2 (List.replicate 2 0) *
    Assn.list pTail2 (List.replicate cap 0) *
    Assn.list pHead2 (List.replicate cap 0) *
    Assn.list pCapPtr2 (List.replicate cap 0) *
    Assn.list pCapLen2 (List.replicate cap 0) *
    Assn.list pCostSign2 (List.replicate cap 0) *
    Assn.list pCostPtr2 (List.replicate cap 0) *
    Assn.list pCostLen2 (List.replicate cap 0) *
    Assn.list pOrigIdx2 (List.replicate cap 0) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pCapBuf2 + e * d.L) (List.replicate d.L 0)) *
    Assn.list pCostBuf2 (List.replicate bufCap 0) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pHFwd + e * d.L) (List.replicate d.L 0)) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pHRev + e * d.L) (List.replicate d.L 0)) *
    Assn.free h (2 ^ w - h)
  post := fun d args h' => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ)
      (pIn2 : ℕ) (pOut2 : ℕ) (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ)
      (pCapBuf2 : ℕ) (pCostBuf2 : ℕ) (pHFwd : ℕ) (pHRev : ℕ) (h : ℕ)
      (g : Fin (d.I.m + d.I.m) → ℤ),
    let k := narrowLimbWidth d.I
    let R := (FlowReduction.shiftedGraph d.I d.hv).residual d.f
    let R' := R.withoutZeroEdges
    ⌜args = [pEdges, pShCapBuf, pFeasFlow, d.I.n, d.I.m, d.L, k,
        pIn2, pOut2, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2,
        pOrigIdx2, pCapBuf2, pCostBuf2, pHFwd, pHRev, h] ∧
      h ≤ h' ∧ h' ≤ h + stage1CircSpace R' k S ∧
      R.Optimal (fun a => (g a : ℝ)) ∧
      (∀ e : Fin d.I.m, 0 ≤ g (Fin.castAdd d.I.m e) ∧ 0 ≤ g (Fin.natAdd d.I.m e)) ∧
      (∀ e : Fin d.I.m, (g (Fin.natAdd d.I.m e)).toNat ≤ (d.f e).toNat) ∧
      (∀ e : Fin d.I.m, (d.f e).toNat + (g (Fin.castAdd d.I.m e)).toNat ≤
        (FlowReduction.shiftedGraph d.I d.hv).capacity e)⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pHFwd + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (g (Fin.castAdd d.I.m ⟨e, hlt⟩)).toNat) d.L else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pHRev + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (g (Fin.natAdd d.I.m ⟨e, hlt⟩)).toNat) d.L else [])) *
    Assn.free h' (2 ^ w - h') * Assn.gc

private def holdAssnRes (A : Assn) : Assn := A

private def resStage1Rest (R' : Circulation) (k : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pIn2 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) : Assn :=
  Assn.list pIn2 [R'.n, R'.m, k, pTail, pHead, pCapPtrs, pCapLens, pCostSign, pCostPtrs, pCostLens] *
  Assn.list pTail (List.ofFn fun e : Fin R'.m => (R'.tail e).val) *
  Assn.list pHead (List.ofFn fun e : Fin R'.m => (R'.head e).val) *
  Assn.list pCapPtrs capPtrs *
  Assn.list pCapLens (capLimbs.map List.length) *
  Assn.list pCostSign (List.ofFn fun e : Fin R'.m => if R'.cost e < 0 then 1 else 0) *
  Assn.list pCostPtrs costPtrs *
  Assn.list pCostLens (costLimbs.map List.length) *
  (∏ j ∈ Finset.range R'.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j []))

private theorem resStage1Rest_noDebt (R' : Circulation) (k : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pIn2 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) :
    Assn.NoDebt (resStage1Rest R' k capPtrs capLimbs costPtrs costLimbs
      pIn2 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens) := by
  unfold resStage1Rest
  exact ((((((((Assn.noDebt_list _ _).mul (Assn.noDebt_list _ _)).mul (Assn.noDebt_list _ _)).mul
    (Assn.noDebt_list _ _)).mul (Assn.noDebt_list _ _)).mul (Assn.noDebt_list _ _)).mul
    (Assn.noDebt_list _ _)).mul (Assn.noDebt_list _ _)).mul
    (Assn.noDebt_prod _ fun _ _ => Assn.noDebt_list _ _)

private theorem stage1Input_eq_cap_rest (R' : Circulation) (k : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pIn2 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) :
    stage1Input R' k capPtrs capLimbs costPtrs costLimbs
      pIn2 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens =
    (∏ j ∈ Finset.range R'.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
    resStage1Rest R' k capPtrs capLimbs costPtrs costLimbs
      pIn2 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens := by
  unfold stage1Input resStage1Rest; ac_rfl

theorem stage0ResWork_meets {w : ℕ} {p : Program} {S : ℕ → ℕ → ℕ}
    {f resBuild resRun : ℕ}
    {Tb : ResBuildData → ℕ} {Tr : Stage0ResRunData → ℕ}
    (hp : p.procs[f]? = some (stage0ResWork resBuild resRun))
    (hb : Meets w p resBuild ((stage0ResBuildSpec w).withCost fun d _ => Tb d))
    (hr : Meets w p resRun ((stage0ResRunSpec w S).withCost fun d _ => Tr d))
    (hTr_indep : ∀ (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
      (hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
      (L : ℕ) (hLge : narrowMaxCapLimbs I + 1 ≤ L) (a b c : ℕ),
      Tr ⟨I, hv, f, hf, L, hLge, a, b, c⟩ = Tr ⟨I, hv, f, hf, L, hLge, 0, 0, 0⟩) :
    Meets w p f ((stage0ResWorkSpec w S).withCost fun d _ =>
      Tb ⟨d.I, d.hv, d.f, d.hf, d.L, 0⟩ + Tr ⟨d.I, d.hv, d.f, d.hf, d.L, d.hLge, 0, 0, 0⟩ + 60) := by
  sep_enter d with hLlt h2k1 hclip hpE h11m hpSC hpFF hmL hpIn2 hpOut2
    hpT hpH hpCP hpCL hpCS hpCoP hpCoL hpOI hcapW hpCB2 hpCoB hbufW hpHF hpHR hn1W hfit1
  have hLge : narrowMaxCapLimbs d.I + 1 ≤ d.L := d.hLge
  set k := narrowLimbWidth d.I
  set R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth d.I
  have hb2k : 1 < 2 ^ k := by have := two_le_pow hk1; omega
  have hL1 : 1 ≤ d.L := by omega
  have hLW : d.L < 2 ^ w := lt_of_lt_of_le hLlt (Nat.pow_le_pow_right (by decide) (by omega))
  have h2U_le_bud : 2 * d.I.maxCapacity ≤ FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity := by
    unfold FlowReduction.scalingCapacityBudget
    have : 2 * (d.I.m + 1) * d.I.maxCapacity = 2 * d.I.m * d.I.maxCapacity + 2 * d.I.maxCapacity := by ring
    omega
  have hbud_lt : FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity < (2 ^ k) ^ d.L :=
    lt_of_lt_of_le (scalingCapacityBudget_lt_pow d.I d.hv)
      (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb2k) hLge)
  have hshCapLen : ∀ e : Fin d.I.m,
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length ≤ d.L := fun e => by
    have hcap := FlowReduction.shiftedGraph_capacity_le d.I d.hv d.I.maxCapacity
      (lower_natAbs_le_maxCapacity' d.I) (upper_natAbs_le_maxCapacity' d.I) e
    exact digits_len_le_of_lt_pow hb2k (lt_of_le_of_lt (le_trans hcap h2U_le_bud) hbud_lt)
  have hfwdLen : ∀ e : Fin d.I.m,
      (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length ≤ d.L :=
    fun e => by
      have ⟨h0, hle⟩ := d.hf e
      exact le_trans (digits_length_mono hb2k (by omega)) (hshCapLen e)
  have hrevLen : ∀ e : Fin d.I.m, (Nat.digits (2 ^ k) (d.f e).toNat).length ≤ d.L := fun e => by
    have ⟨h0, hle⟩ := d.hf e
    exact le_trans (digits_length_mono hb2k (by omega)) (hshCapLen e)
  have hcapLen_le : ∀ j (hj : j < R'.m), ((resCapLimbs d.I d.hv d.f).getD j []).length ≤ d.L := fun j hj => by
    have hget : (resCapLimbs d.I d.hv d.f).getD j [] = Nat.digits (2 ^ k) (R'.capacity ⟨j, hj⟩) := by
      rw [List.getD_eq_getElem _ _ (by rw [resCapLimbs_length]; exact hj)]
      simp [resCapLimbs, R', k]
    have hle := le_trans (Finset.le_sup (f := R'.capacity) (Finset.mem_univ (⟨j, hj⟩ : Fin R'.m)))
      (residual_withoutZeroEdges_maxCapacity_le d.I d.hv d.f d.hf)
    rw [hget]
    exact digits_len_le_of_lt_pow hb2k (lt_of_le_of_lt (le_trans hle h2U_le_bud) hbud_lt)
  have hcapSpec := resCapLimbs_spec d.I d.hv d.f hk3 h2k1 hLlt hcapLen_le
  have hcostSpec := resCostLimbs_spec d.I d.hv d.f hk3 h2k1
  sep_apply (list_join_two pOut2 0 0).symm
  generalize hF1 :
    ((pOut2 + 1 ↦ 0) *
     (∏ e ∈ Finset.range d.I.m, Assn.list (pHFwd + e * d.L) (List.replicate d.L 0)) *
     (∏ e ∈ Finset.range d.I.m, Assn.list (pHRev + e * d.L) (List.replicate d.L 0)) *
     Assn.free h (2 ^ w - h)) = F1
  sep_apply hF1
  sep_step from (⟨d.I, d.hv, d.f, d.hf, d.L, 0⟩ : ResBuildData)
  sep_step
  subst F1; sep_norm
  sep_apply list_join_two pOut2 R'.m 0
  obtain ⟨R_cap, hcap_split0⟩ :=
    res_split_capBuf_feasFlow d.I d.hv d.f pCapBuf2 pFeasFlow d.L hfwdLen hrevLen
  have hcap_split :
      (∏ i ∈ Finset.range d.I.m,
        Assn.list (pCapBuf2 + i * d.L)
          (if hlt : i < d.I.m then
            padLimbs (Nat.digits (2 ^ k)
              (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩ : ℤ) - d.f ⟨i, hlt⟩).toNat) d.L
           else [])) *
      (∏ i ∈ Finset.range d.I.m,
        Assn.list (pFeasFlow + i * d.L)
          (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) =
      (∏ j ∈ Finset.range R'.m,
        Assn.list ((resCapPtrs d.I d.hv d.f pCapBuf2 pFeasFlow d.L).getD j 0)
          ((resCapLimbs d.I d.hv d.f).getD j [])) * holdAssnRes R_cap := hcap_split0
  sep_apply hcap_split
  have hfold_in :
      Assn.list pIn2 [R'.n, R'.m, k, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2] *
      Assn.list pTail2 (List.ofFn fun e : Fin R'.m => (R'.tail e).val) *
      Assn.list pHead2 (List.ofFn fun e : Fin R'.m => (R'.head e).val) *
      Assn.list pCapPtr2 (resCapPtrs d.I d.hv d.f pCapBuf2 pFeasFlow d.L) *
      Assn.list pCapLen2 ((resCapLimbs d.I d.hv d.f).map List.length) *
      (∏ j ∈ Finset.range R'.m,
        Assn.list ((resCapPtrs d.I d.hv d.f pCapBuf2 pFeasFlow d.L).getD j 0)
          ((resCapLimbs d.I d.hv d.f).getD j [])) *
      Assn.list pCostSign2 (List.ofFn fun e : Fin R'.m => if R'.cost e < 0 then 1 else 0) *
      Assn.list pCostPtr2 (resCostPtrs d.I d.hv d.f pCostBuf2) *
      Assn.list pCostLen2 ((resCostLimbs d.I d.hv d.f).map List.length) *
      (∏ j ∈ Finset.range R'.m,
        Assn.list ((resCostPtrs d.I d.hv d.f pCostBuf2).getD j 0)
          ((resCostLimbs d.I d.hv d.f).getD j [])) =
      stage1Input R' k (resCapPtrs d.I d.hv d.f pCapBuf2 pFeasFlow d.L) (resCapLimbs d.I d.hv d.f)
        (resCostPtrs d.I d.hv d.f pCostBuf2) (resCostLimbs d.I d.hv d.f)
        pIn2 pTail2 pHead2 pCapPtr2 pCapLen2 pCostSign2 pCostPtr2 pCostLen2 := by
    unfold stage1Input; ac_rfl
  sep_apply hfold_in
  generalize hF2 :
    (Assn.list 0 (narrowEncode d.I) *
     (∏ i ∈ Finset.range d.I.m,
       Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
     (∏ i ∈ Finset.range d.I.m,
       Assn.list (pShCapBuf + i * d.L)
         (if hlt : i < d.I.m then
           padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
         else []))) = F2
  sep_apply hF2
  have hTr_eq : Tr ⟨d.I, d.hv, d.f, d.hf, d.L, d.hLge, pCapBuf2, pFeasFlow, pCostBuf2⟩ =
      Tr ⟨d.I, d.hv, d.f, d.hf, d.L, d.hLge, 0, 0, 0⟩ :=
    hTr_indep d.I d.hv d.f d.hf d.L d.hLge pCapBuf2 pFeasFlow pCostBuf2
  sep_step from (⟨d.I, d.hv, d.f, d.hf, d.L, d.hLge, pCapBuf2, pFeasFlow, pCostBuf2⟩ : Stage0ResRunData)
    with hh1_lo hh1_hi hopt_g hg_nn hg_rev hg_fwd
  sep_apply stage1Input_eq_cap_rest R' k (resCapPtrs d.I d.hv d.f pCapBuf2 pFeasFlow d.L) (resCapLimbs d.I d.hv d.f)
    (resCostPtrs d.I d.hv d.f pCostBuf2) (resCostLimbs d.I d.hv d.f)
    pIn2 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens
  sep_apply hcap_split.symm
  sep_apply (resStage1Rest_noDebt R' k (resCapPtrs d.I d.hv d.f pCapBuf2 pFeasFlow d.L) (resCapLimbs d.I d.hv d.f)
    (resCostPtrs d.I d.hv d.f pCostBuf2) (resCostLimbs d.I d.hv d.f)
    pIn2 pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens).le_gc
  sep_apply (Assn.noDebt_prod (Finset.range d.I.m) fun i _ =>
    Assn.noDebt_list (pCapBuf2 + i * d.L)
      (if hlt : i < d.I.m then
        padLimbs (Nat.digits (2 ^ k)
          (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩ : ℤ) - d.f ⟨i, hlt⟩).toNat) d.L
      else [])).le_gc
  subst F2; sep_norm
  sep_step

end MinCostFlow.NarrowProg
