module

public import WordRAM.Module
public import MinCostFlow.Narrow.Defs
public import MinCostFlow.Narrow.BitScalingModel
public import MinCostFlow.NarrowProg.SolverBridge
public import MinCostFlow.NarrowProg.PhaseWrite
public import MinCostFlow.NarrowProg.PhaseState
public import MinCostFlow.NarrowProg.PhaseUpdate
public import MinCostFlow.NarrowProg.BitScaleFinalize
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Stage 2 phase loop (`bitScaleLoop`)

Executes the `T = bitScalingPhases I` phases of Gabow bit scaling: in each phase `t < T`,
writes `(bitScalePhaseInstance I T t g).positiveInstance.solverWords` via `phaseWrite`, invokes
the circulation solver via `solverSpec`, updates `ρ̃`, `g̃`, `posAcc`, and `negAcc` via
`phaseUpdate`, and advances the heap pointer `curH` without zeroing solver scratch.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

private theorem split_free_phase {curH bufLen w : ℕ} (hfit : curH + bufLen ≤ 2 ^ w) :
    Assn.free curH (2 ^ w - curH) =
      Assn.list curH (List.replicate bufLen 0) *
      Assn.free (curH + bufLen) (2 ^ w - (curH + bufLen)) := by
  have hsplit : 2 ^ w - curH = bufLen + (2 ^ w - (curH + bufLen)) := by omega
  rw [hsplit, Assn.free_add', Assn.free]

private theorem cappedResidual_zero_eq {I : Circulation} {T : ℕ}
    (hT : ∀ e, I.capacity e < 2 ^ T) (e : Fin I.m) :
    cappedResidual I T 0 (fun _ => 0) (I.m + 1) e = 0 := by
  simp only [cappedResidual, phaseResidual, Nat.sub_zero, Nat.div_eq_of_lt (hT e)]
  simp

private theorem cappedFlow_zero_eq (I : Circulation) (e : Fin I.m) :
    cappedFlow (fun _ : Fin I.m => (0 : ℤ)) (I.m + 1) e = 0 := by
  simp [cappedFlow]

/-- Named value for `bitScaleLoopSpec`. -/
structure BitScaleLoopData where
  I : Circulation
  k : ℕ
  capPtrs : List ℕ
  capLimbs : List (List ℕ)
  ptrs : BitScalePtrs
  pRho : ℕ
  pGCap : ℕ
  pPosAcc : ℕ
  pNegAcc : ℕ

/-- Run the `T = bitScalingPhases I` bit-scaling phases starting from zeroed `pRho`, `pGCap`,
`pPosAcc`, `pNegAcc`, returning the updated heap pointer `curH'`. -/
wram_def bitScaleLoop (pw sol pu mx : ℕ) (pIn, pState, T, curH) {
  m := mem[pIn + 1]
  pRho := mem[pState]
  pGCap := mem[pState + 1]
  t := 0
  while t < T {
    shift := T - 1 - t
    hIn := curH + 2 + 10 * m
    r := pw(pIn, pRho, pGCap, shift, curH)
    v := sol(curH, hIn)
    r := pu(pIn, pState, hIn, shift)
    curH := mx(hIn + 2 * m, v)
    t := t + 1
  }
  return curH
}

/-- Specification of `bitScaleLoop`: runs `T = bitScalingPhases I` phases and outputs ghost
integral optimum `g` of `I` together with the final capped residual/flow arrays and lazy
accumulators `posAcc`/`negAcc`. -/
def bitScaleLoopSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec BitScaleLoopData where
  pre d args := ⨆ (pIn : ℕ) (pState : ℕ) (curH0 : ℕ),
    let T := bitScalingPhases d.I
    let L := T / d.k + 2
    let stepS := 2 + 12 * d.I.m + S (d.I.n + 1) (2 * d.I.m)
    ⌜args = [pIn, pState, T, curH0] ∧
      d.capPtrs.length = d.I.m ∧ d.capLimbs.length = d.I.m ∧
      (∀ j (hj : j < d.I.m), Limbs d.k (d.capLimbs.getD j []) ∧
        Nat.ofDigits (2 ^ d.k) (d.capLimbs.getD j []) = d.I.capacity ⟨j, hj⟩) ∧
      1 ≤ d.k ∧ 2 * d.k ≤ w ∧ d.k + Nat.log 2 (2 * d.k) + 2 ≤ w ∧
      d.I.m + 1 < 2 ^ d.k ∧ 5 * d.I.m + 9 < 2 ^ w ∧ d.I.n + 1 < 2 ^ w ∧
      d.I.m * L < 2 ^ w ∧ d.pPosAcc + d.I.m * L ≤ 2 ^ w ∧ d.pNegAcc + d.I.m * L ≤ 2 ^ w ∧
      d.I.CostsBounded ((2 * d.I.m) ^ 10) ∧ (∀ e, (d.I.cost e).natAbs < 2 ^ w) ∧
      curH0 + T * stepS < 2 ^ w⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pState [d.pRho, d.pGCap, d.pPosAcc, d.pNegAcc, L] *
    Assn.list d.pRho (List.replicate d.I.m 0) *
    Assn.list d.pGCap (List.replicate d.I.m 0) *
    (∏ j ∈ Finset.range d.I.m, Assn.list (d.pPosAcc + j * L) (List.replicate L 0)) *
    (∏ j ∈ Finset.range d.I.m, Assn.list (d.pNegAcc + j * L) (List.replicate L 0)) *
    Assn.free curH0 (2 ^ w - curH0)
  post d args curH' := ⨆ (pIn : ℕ) (pState : ℕ) (curH0 : ℕ)
      (g : Fin d.I.m → ℤ) (posAcc : Fin d.I.m → List ℕ) (negAcc : Fin d.I.m → List ℕ),
    let T := bitScalingPhases d.I
    let L := T / d.k + 2
    let stepS := 2 + 12 * d.I.m + S (d.I.n + 1) (2 * d.I.m)
    ⌜args = [pIn, pState, T, curH0] ∧ curH0 ≤ curH' ∧ curH' ≤ curH0 + T * stepS ∧
      d.I.Optimal (fun e => (g e : ℝ)) ∧
      (∀ e : Fin d.I.m, (posAcc e).length = L ∧ (negAcc e).length = L) ∧
      (∀ e : Fin d.I.m, ∀ j < L,
        (posAcc e).getD j 0 ≤ accTouches d.k T T j * (2 ^ d.k - 1) ∧
        (negAcc e).getD j 0 ≤ accTouches d.k T T j * (2 ^ d.k - 1)) ∧
      (∀ e : Fin d.I.m,
        ((Nat.ofDigits (2 ^ d.k) (posAcc e) : ℕ) : ℤ) -
          ((Nat.ofDigits (2 ^ d.k) (negAcc e) : ℕ) : ℤ) = g e) ∧
      (∀ e : Fin d.I.m,
        Nat.ofDigits (2 ^ d.k) (posAcc e) ≤ (d.I.m + 1) * (2 ^ T - 1) ∧
        Nat.ofDigits (2 ^ d.k) (negAcc e) ≤ (d.I.m + 1) * (2 ^ T - 1))⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pState [d.pRho, d.pGCap, d.pPosAcc, d.pNegAcc, L] *
    Assn.list d.pRho (List.ofFn fun e => cappedResidual d.I T T g (d.I.m + 1) e) *
    Assn.list d.pGCap (List.ofFn fun e => cappedFlow g (d.I.m + 1) e) *
    (∏ j ∈ Finset.range d.I.m,
      Assn.list (d.pPosAcc + j * L) (if h : j < d.I.m then posAcc ⟨j, h⟩ else [])) *
    (∏ j ∈ Finset.range d.I.m,
      Assn.list (d.pNegAcc + j * L) (if h : j < d.I.m then negAcc ⟨j, h⟩ else [])) *
    Assn.free curH' (2 ^ w - curH')

private structure PhaseLoopState (I : Circulation) where
  t : ℕ
  g : Fin I.m → ℤ
  posAcc : Fin I.m → List ℕ
  negAcc : Fin I.m → List ℕ
  curH : ℕ
  shift0 : ℕ
  hIn0 : ℕ
  r0 : ℕ
  v0 : ℕ

theorem bitScaleLoop_meets {w : ℕ} {p : Program} {f pw sol pu mx : ℕ}
    {Tsol S : ℕ → ℕ → ℕ} {Tpw Tpu : ℕ → ℕ}
    (hp : p.procs[f]? = some (bitScaleLoop pw sol pu mx))
    (hpw : Meets w p pw ((phaseWriteSpec w).withCost fun d _ => Tpw d.I.m))
    (hsol : Meets w p sol ((solverSpec w S).withCost fun J _ => Tsol J.n J.m))
    (hpu : Meets w p pu ((phaseUpdateSpec w).withCost fun d _ => Tpu d.I.m))
    (hmx : Meets w p mx ((max2Spec w).withCost fun _ _ => 20)) :
    Meets w p f ((bitScaleLoopSpec w S).withCost fun d _ =>
      bitScalingPhases d.I * (Tpw d.I.m + Tsol (d.I.n + 1) (2 * d.I.m) + Tpu d.I.m + 100) + 80) := by
  sep_enter ⟨I, k, capPtrs, capLimbs, ⟨pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens⟩,
    pRho, pGCap, pPosAcc, pNegAcc⟩ with
    hptrs hlimbs hcaps hk h2kw hkw hm_lt hw hn hmL hpPos_fit hpNeg_fit hcostB hcostW hcur_fit
  set T := bitScalingPhases I
  set L := T / k + 2
  set stepS := 2 + 12 * I.m + S (I.n + 1) (2 * I.m)
  set Cphase := Tpw I.m + Tsol (I.n + 1) (2 * I.m) + Tpu I.m + 100
  sep_apply bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens
  sep_step
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hm
  subst m
  sep_apply (bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens).symm
  sep_step; sep_step
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpRho_1 hpGCap_1
  subst pRho_1 pGCap_1
  sep_step
  have hT_cap : ∀ e : Fin I.m, I.capacity e < 2 ^ T := capacity_lt_two_pow_bitScalingPhases I
  have hrho_init : Assn.list pRho (List.replicate I.m 0) =
      Assn.list pRho (List.ofFn fun e : Fin I.m => cappedResidual I T 0 (fun _ => 0) (I.m + 1) e) := by
    congr 1
    apply List.ext_getElem (by simp)
    intro j hj1 hj2
    simp [cappedResidual_zero_eq hT_cap]
  have hgcap_init : Assn.list pGCap (List.replicate I.m 0) =
      Assn.list pGCap (List.ofFn fun e : Fin I.m => cappedFlow (fun _ : Fin I.m => (0 : ℤ)) (I.m + 1) e) := by
    congr 1
    apply List.ext_getElem (by simp)
    intro j hj1 hj2
    simp [cappedFlow_zero_eq I]
  have hpos_init : (∏ j ∈ Finset.range I.m, Assn.list (pPosAcc + j * L) (List.replicate L 0)) =
      (∏ j ∈ Finset.range I.m,
        Assn.list (pPosAcc + j * L) (if _ : j < I.m then List.replicate L 0 else [])) := by
    refine Finset.prod_congr rfl fun j hj => by simp [Finset.mem_range.mp hj]
  have hneg_init : (∏ j ∈ Finset.range I.m, Assn.list (pNegAcc + j * L) (List.replicate L 0)) =
      (∏ j ∈ Finset.range I.m,
        Assn.list (pNegAcc + j * L) (if _ : j < I.m then List.replicate L 0 else [])) := by
    refine Finset.prod_congr rfl fun j hj => by simp [Finset.mem_range.mp hj]
  sep_apply hrho_init
  sep_apply hgcap_init
  sep_apply hpos_init
  sep_apply hneg_init
  let a₀ : PhaseLoopState I :=
    { t := 0, g := fun _ => 0, posAcc := fun _ => List.replicate L 0,
      negAcc := fun _ => List.replicate L 0, curH := curH0,
      shift0 := 0, hIn0 := 0, r0 := 0, v0 := 0 }
  have ht0 : a₀.t ≤ T := Nat.zero_le T
  have hcur0_ge : curH0 ≤ a₀.curH := le_rfl
  have hcur0_le : a₀.curH ≤ curH0 + a₀.t * stepS := by simp [a₀]
  have hopt0 : (truncInstance I (T - a₀.t)).Optimal (fun e => (a₀.g e : ℝ)) := by
    simpa only [a₀, Nat.sub_zero, Int.cast_zero] using truncInstance_zero_optimal I T hT_cap
  have hlen0 : ∀ e : Fin I.m, (a₀.posAcc e).length = L ∧ (a₀.negAcc e).length = L := fun _ => by
    simp [a₀]
  have hbd0 : ∀ e : Fin I.m, ∀ j < L,
      (a₀.posAcc e).getD j 0 ≤ accTouches k T a₀.t j * (2 ^ k - 1) ∧
      (a₀.negAcc e).getD j 0 ≤ accTouches k T a₀.t j * (2 ^ k - 1) := fun _ _ _ => by
    simp [a₀, accTouches_zero]
  have hdiff0_init : ∀ e : Fin I.m,
      ((Nat.ofDigits (2 ^ k) (a₀.posAcc e) : ℕ) : ℤ) -
        ((Nat.ofDigits (2 ^ k) (a₀.negAcc e) : ℕ) : ℤ) = a₀.g e * (2 : ℤ) ^ (T - a₀.t) :=
    fun _ => by simp [a₀, Nat.ofDigits_replicate_zero]
  have hval0_init : ∀ e : Fin I.m,
      Nat.ofDigits (2 ^ k) (a₀.posAcc e) ≤ (I.m + 1) * (2 ^ T - 2 ^ (T - a₀.t)) ∧
      Nat.ofDigits (2 ^ k) (a₀.negAcc e) ≤ (I.m + 1) * (2 ^ T - 2 ^ (T - a₀.t)) :=
    fun _ => by simp [a₀, Nat.ofDigits_replicate_zero]
  sep_while (fun s : PhaseLoopState I =>
    ⟨[pIn, pState, T, s.curH, I.m, pRho, pGCap, s.t, s.shift0, s.hIn0, s.r0, s.v0],
      s.t ≤ T ∧ curH0 ≤ s.curH ∧ s.curH ≤ curH0 + s.t * stepS ∧
      (truncInstance I (T - s.t)).Optimal (fun e => (s.g e : ℝ)) ∧
      (∀ e : Fin I.m, (s.posAcc e).length = L ∧ (s.negAcc e).length = L) ∧
      (∀ e : Fin I.m, ∀ j < L,
        (s.posAcc e).getD j 0 ≤ accTouches k T s.t j * (2 ^ k - 1) ∧
        (s.negAcc e).getD j 0 ≤ accTouches k T s.t j * (2 ^ k - 1)) ∧
      (∀ e : Fin I.m,
        ((Nat.ofDigits (2 ^ k) (s.posAcc e) : ℕ) : ℤ) -
          ((Nat.ofDigits (2 ^ k) (s.negAcc e) : ℕ) : ℤ) = s.g e * (2 : ℤ) ^ (T - s.t)) ∧
      (∀ e : Fin I.m,
        Nat.ofDigits (2 ^ k) (s.posAcc e) ≤ (I.m + 1) * (2 ^ T - 2 ^ (T - s.t)) ∧
        Nat.ofDigits (2 ^ k) (s.negAcc e) ≤ (I.m + 1) * (2 ^ T - 2 ^ (T - s.t))),
      (Cphase : ℤ) * ((T : ℤ) - (s.t : ℤ)) + 20,
      [bitScaleInput I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens,
       Assn.list pState [pRho, pGCap, pPosAcc, pNegAcc, L],
       Assn.list pRho (List.ofFn fun e => cappedResidual I T s.t s.g (I.m + 1) e),
       Assn.list pGCap (List.ofFn fun e => cappedFlow s.g (I.m + 1) e),
       ∏ j ∈ Finset.range I.m,
         Assn.list (pPosAcc + j * L) (if h : j < I.m then s.posAcc ⟨j, h⟩ else []),
       ∏ j ∈ Finset.range I.m,
         Assn.list (pNegAcc + j * L) (if h : j < I.m then s.negAcc ⟨j, h⟩ else []),
       Assn.free s.curH (2 ^ w - s.curH)]⟩)
    (fun s => T - s.t) from a₀ with ⟨t, g, posAcc, negAcc, curH, shift0, hIn0, r0, v0⟩
  · have hstep_fit : curH + stepS < 2 ^ w := by
      have h1 : (t + 1) * stepS ≤ T * stepS := Nat.mul_le_mul_right stepS (by omega)
      have h2 : curH + stepS ≤ curH0 + (t + 1) * stepS := by rw [Nat.succ_mul]; omega
      omega
    have hbuf_fit : curH + (2 + 10 * I.m) < 2 ^ w := by dsimp only [stepS] at hstep_fit; omega
    have h10 : 10 < 2 ^ w := by
      have h9 : 9 < 2 ^ w := by omega
      have hw4 : 4 ≤ w := by
        by_contra hlt
        interval_cases w <;> omega
      have h16 : 2 ^ 4 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw4
      omega
    sep_step
    sep_step
    sep_apply split_free_phase (curH := curH) (bufLen := 2 + 10 * I.m) (w := w) (by omega)
    have hshift_eq : shift = T - (t + 1) := by omega
    have hg_bounds : ∀ e, 0 ≤ g e ∧ g e ≤ ((truncInstance I (T - t)).capacity e : ℤ) := by
      intro e
      have h1 : 0 ≤ g e := (Int.cast_nonneg_iff (R := ℝ)).mp (hinv_3.1.2 e).1
      have h2 : g e ≤ ((truncInstance I (T - t)).capacity e : ℤ) := by
        apply (Int.cast_le (R := ℝ)).mp
        simpa only [Int.cast_natCast] using (hinv_3.1.2 e).2
      exact ⟨h1, h2⟩
    sep_step from (⟨I, k, capPtrs, capLimbs, ⟨pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens⟩,
      T, t, g, List.replicate (2 + 10 * I.m) 0⟩ : PhaseWriteData)
    set J := (bitScalePhaseInstance I T t g).positiveInstance
    obtain ⟨hJn, hJm, hJlen, hJwords, hJcost, hJcap⟩ :=
      positivePhase_solver_pre (T := T) (t := t) (g := g) hn hw hcostB hcostW
    have hJfit : curH + J.solverWords.length + J.m + S J.n J.m < 2 ^ w := by
      rw [hJlen, hJm, hJn]; dsimp only [stepS] at hstep_fit; omega
    have hhIn_J : hIn = curH + J.solverWords.length := by rw [hhIn, hJlen]; omega
    sep_step from J with _ hv_ge hv_le hflow_len hsol_opt
    have hflow_len' : flow.length = 2 * I.m := by rw [hflow_len, hJm]
    sep_step from (⟨I, k, capPtrs, capLimbs, ⟨pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens⟩,
      pRho, pGCap, pPosAcc, pNegAcc, T, t, g, flow, posAcc, negAcc⟩ : PhaseUpdateData) with
      hg_opt' hacc_len' hacc_bd' hacc_diff' hacc_val'
    have hhIn_2m_lt : hIn + 2 * I.m < 2 ^ w := by omega
    sep_step from (hIn + 2 * I.m, v)
    sep_step
    have hcur_next_le : max (hIn + 2 * I.m) v ≤ curH0 + (t + 1) * stepS := by
      have hv_step : v ≤ curH + stepS := by
        rw [hJlen, hJm, hJn] at hv_le
        dsimp only [stepS]; omega
      have hsucc : (t + 1) * stepS = t * stepS + stepS := Nat.succ_mul t stepS
      have hbuf2 : hIn + 2 * I.m ≤ curH + stepS := by
        rw [hhIn]; dsimp only [stepS]; omega
      omega
    have hfree_eq : Assn.free (max v (curH + J.solverWords.length + J.m))
          (2 ^ w - max v (curH + J.solverWords.length + J.m)) =
        Assn.free (max (hIn + 2 * I.m) v) (2 ^ w - max (hIn + 2 * I.m) v) := by
      rw [Nat.max_comm v _, hhIn, hJlen, hJm]; congr 1 <;> omega
    have hTsol_eq : Tsol J.n J.m = Tsol (I.n + 1) (2 * I.m) := by rw [hJn, hJm]
    sep_apply hfree_eq
    rw [hTsol_eq]
    sep_exists (⟨t + 1, nextGhostFlow I T t g flow, nextPosAcc I k T t g flow posAcc,
      nextNegAcc I k T t g flow negAcc, max (hIn + 2 * I.m) v, shift, hIn, 0, v⟩ : PhaseLoopState I)
    · dsimp only [Cphase]; simp only [Nat.cast_add, Nat.cast_one]; ring_nf; omega
  · have ht_eq : t = T := by omega
    subst ht_eq
    have hg_I_opt : I.Optimal (fun e => (g e : ℝ)) := by
      have h0 := hinv_3
      rw [Nat.sub_self] at h0
      cases I with
      | mk n m tail head cap cost =>
        dsimp only [truncInstance] at h0
        have hcap : (fun e : Fin m => cap e / 2 ^ 0) = cap := funext fun e => by simp
        rwa [hcap] at h0
    have hdiff0 : ∀ e : Fin I.m,
        ((Nat.ofDigits (2 ^ k) (posAcc e) : ℕ) : ℤ) -
          ((Nat.ofDigits (2 ^ k) (negAcc e) : ℕ) : ℤ) = g e := by
      intro e
      simpa only [Nat.sub_self, pow_zero, mul_one] using hinv_6 e
    have hval0 : ∀ e : Fin I.m,
        Nat.ofDigits (2 ^ k) (posAcc e) ≤ (I.m + 1) * (2 ^ T - 1) ∧
        Nat.ofDigits (2 ^ k) (negAcc e) ≤ (I.m + 1) * (2 ^ T - 1) := by
      intro e
      simpa only [Nat.sub_self, pow_zero] using hinv_7 e
    sep_step

end MinCostFlow.NarrowProg
