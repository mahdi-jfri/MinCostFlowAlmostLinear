module

public import WordRAM.Module
public import WordRAM.Std.Bits
public import WordRAM.Std.Limbs
public import MinCostFlow.Narrow.Defs
public import MinCostFlow.Narrow.BitScalingModel
public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.NarrowProg.LimbBit
public import MinCostFlow.NarrowProg.TopBitLength
public import MinCostFlow.NarrowProg.AccAdd
public import MinCostFlow.NarrowProg.AccNormalize
public import MinCostFlow.NarrowProg.SolverBridge
public import MinCostFlow.NarrowProg.PhaseWrite
public import MinCostFlow.NarrowProg.PhaseState
public import MinCostFlow.NarrowProg.PhaseUpdate
public import MinCostFlow.NarrowProg.BitScaleFinalize
public import MinCostFlow.NarrowProg.BitScaleLoop
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Stage 2: Gabow bit scaling in narrow words (`bitScale`)

Implements and verifies Stage 2 of the narrow-word outer algorithm (`notes/narrow_words_design.md`):
given a circulation `I` with `k`-bit canonical capacity limbs and polynomial costs
(`I.CostsBounded ((2 * I.m) ^ 10)`), `bitScale` computes `T = bitScalingPhases I` via
`topBitLength`, allocates zeroed working arrays from `Assn.free`, runs the `T` phases via
`bitScaleLoop` (calling `phaseWrite`, the external bounded circulation solver `solver`, and
`phaseUpdate`), and normalizes/subtracts the lazy accumulators into normalized `L`-limb
(`L = T / k + 2`) base-`2 ^ k` flow representations via `bitScaleFinalize`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Scaling.Machine
  MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Heap-splitting helpers -/

private theorem list_split_four {p : ℕ} {buf : List ℕ} (hlen : buf.length = 4) :
    Assn.list p buf =
      (p ↦ buf[0]'(by omega)) * (p + 1 ↦ buf[1]'(by omega)) *
      (p + 2 ↦ buf[2]'(by omega)) * (p + 3 ↦ buf[3]'(by omega)) := by
  rcases buf with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | xs⟩⟩⟩⟩ <;> simp at hlen ⊢
  simp only [mul_assoc, show p + 1 + 1 = p + 2 by omega, show p + 2 + 1 = p + 3 by omega]

private theorem list_join_four (p a0 a1 a2 a3 : ℕ) :
    (p ↦ a0) * (p + 1 ↦ a1) * (p + 2 ↦ a2) * (p + 3 ↦ a3) = Assn.list p [a0, a1, a2, a3] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one, mul_assoc,
    show p + 1 + 1 = p + 2 by omega, show p + 2 + 1 = p + 3 by omega]

private theorem list_split_five_zero (p : ℕ) :
    Assn.list p (List.replicate 5 0) =
      (p ↦ 0) * (p + 1 ↦ 0) * (p + 2 ↦ 0) * (p + 3 ↦ 0) * (p + 4 ↦ 0) := by
  simp only [List.replicate_succ, List.replicate_zero, Assn.list_cons, Assn.list_nil, mul_one,
    mul_assoc, show p + 1 + 1 = p + 2 by omega, show p + 2 + 1 = p + 3 by omega,
    show p + 3 + 1 = p + 4 by omega]

private theorem list_join_five (p a0 a1 a2 a3 a4 : ℕ) :
    (p ↦ a0) * (p + 1 ↦ a1) * (p + 2 ↦ a2) * (p + 3 ↦ a3) * (p + 4 ↦ a4) =
      Assn.list p [a0, a1, a2, a3, a4] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one, mul_assoc,
    show p + 1 + 1 = p + 2 by omega, show p + 2 + 1 = p + 3 by omega,
    show p + 3 + 1 = p + 4 by omega]

private theorem split_free_initial {h m L w : ℕ} (hfit : h + (5 + 2 * m + 3 * m * L) ≤ 2 ^ w) :
    Assn.free h (2 ^ w - h) =
      Assn.list h (List.replicate m 0) *
      Assn.list (h + m) (List.replicate m 0) *
      (∏ j ∈ Finset.range m, Assn.list (h + 2 * m + j * L) (List.replicate L 0)) *
      (∏ j ∈ Finset.range m, Assn.list (h + 2 * m + m * L + j * L) (List.replicate L 0)) *
      (∏ j ∈ Finset.range m, Assn.list (h + 2 * m + 2 * (m * L) + j * L) (List.replicate L 0)) *
      Assn.list (h + 2 * m + 3 * (m * L)) (List.replicate 5 0) *
      Assn.free (h + 2 * m + 3 * (m * L) + 5) (2 ^ w - (h + 2 * m + 3 * (m * L) + 5)) := by
  have h3mL : 3 * (m * L) = 3 * m * L := by ring
  have hsplit : 2 ^ w - h =
      m + (m + (m * L + (m * L + (m * L + (5 + (2 ^ w - (h + 2 * m + 3 * (m * L) + 5))))))) := by
    omega
  rw [hsplit, Assn.free_add', Assn.free_add', Assn.free_add', Assn.free_add', Assn.free_add',
    Assn.free_add']
  rw [← free_mul_eq_prod, ← free_mul_eq_prod, ← free_mul_eq_prod]
  simp only [Assn.free, mul_assoc,
    show h + m + m = h + 2 * m by omega,
    show h + 2 * m + m * L + m * L = h + 2 * m + 2 * (m * L) by omega,
    show h + 2 * m + 2 * (m * L) + m * L = h + 2 * m + 3 * (m * L) by omega]

/-! ### The `bitScale` procedure and specification -/

/-- Named value for `bitScaleSpec`. -/
structure BitScaleData where
  I : Circulation
  k : ℕ
  capPtrs : List ℕ
  capLimbs : List (List ℕ)
  ptrs : BitScalePtrs
  outBuf : List ℕ

/-- Stage 2 (Gabow bit scaling) in narrow words. Calls `topBitLength` (`tl`), `bitScaleLoop`
(`lp`), and `bitScaleFinalize` (`fin`). Returns the final heap pointer `h'`. -/
wram_def bitScale (tl lp fin : ℕ) (pIn, pOut, h) {
  m := mem[pIn + 1]
  k := mem[pIn + 2]
  pCapPtrs := mem[pIn + 7]
  pCapLens := mem[pIn + 8]
  T := tl(pCapPtrs, pCapLens, m, k)
  L := T / k + 2
  pRho := h
  pGCap := h + m
  pFlow := h + 2 * m
  mL := m * L
  pPosAcc := pFlow + mL
  pNegAcc := pFlow + 2 * mL
  pState := pFlow + 3 * mL
  curH := pState + 5
  mem[pOut] := pFlow
  mem[pOut + 1] := L
  mem[pOut + 2] := pRho
  mem[pOut + 3] := pGCap
  mem[pState] := pRho
  mem[pState + 1] := pGCap
  mem[pState + 2] := pPosAcc
  mem[pState + 3] := pNegAcc
  mem[pState + 4] := L
  curH := lp(pIn, pState, T, curH)
  r := fin(pPosAcc, pNegAcc, pFlow, m, L, k)
  return curH
}

/-- Specification of `bitScale`: computes an integral optimum `g` of `I` as normalized `L`-limb
(`L = bitScalingPhases I / k + 2`) base-`2 ^ k` integers at `pFlow`, together with the final
capped residuals `pRho` and capped flows `pGCap` whose positive entries match positive residual
capacities of `I`. -/
def bitScaleSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec BitScaleData where
  pre d args := ⨆ (pIn : ℕ) (pOut : ℕ) (h : ℕ),
    ⌜args = [pIn, pOut, h] ∧ d.outBuf.length = 4 ∧
      d.capPtrs.length = d.I.m ∧ d.capLimbs.length = d.I.m ∧
      (∀ j (hj : j < d.I.m), CanonicalLimbs d.k (d.capLimbs.getD j []) ∧
        (d.capLimbs.getD j []).length * d.k < 2 ^ w ∧
        Nat.ofDigits (2 ^ d.k) (d.capLimbs.getD j []) = d.I.capacity ⟨j, hj⟩) ∧
      1 ≤ d.k ∧ 2 * d.k ≤ w ∧ d.k + Nat.log 2 (2 * d.k) + 2 ≤ w ∧
      d.I.m + 1 < 2 ^ d.k ∧ 5 * d.I.m + 9 < 2 ^ w ∧ d.I.n + 1 < 2 ^ w ∧
      d.I.CostsBounded ((2 * d.I.m) ^ 10) ∧ (∀ e, (d.I.cost e).natAbs < 2 ^ w) ∧
      h + bitScaleSpace d.I d.k S < 2 ^ w⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pOut d.outBuf * Assn.free h (2 ^ w - h)
  post d args h' := ⨆ (pIn : ℕ) (pOut : ℕ) (h : ℕ)
      (g : Fin d.I.m → ℤ) (flowLimbs : Fin d.I.m → List ℕ),
    let T := bitScalingPhases d.I
    let L := T / d.k + 2
    let pRho := h
    let pGCap := h + d.I.m
    let pFlow := h + 2 * d.I.m
    ⌜args = [pIn, pOut, h] ∧ h ≤ h' ∧ h' ≤ h + bitScaleSpace d.I d.k S ∧
      d.I.Optimal (fun e => (g e : ℝ)) ∧
      (∀ e, 0 ≤ g e ∧ Limbs d.k (flowLimbs e) ∧ (flowLimbs e).length = L ∧
        ((Nat.ofDigits (2 ^ d.k) (flowLimbs e) : ℕ) : ℤ) = g e) ∧
      (∀ e, (0 < cappedResidual d.I T T g (d.I.m + 1) e ↔
          0 < (d.I.residual g).capacity (Fin.castAdd d.I.m e)) ∧
        (0 < cappedFlow g (d.I.m + 1) e ↔
          0 < (d.I.residual g).capacity (Fin.natAdd d.I.m e)))⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pOut [pFlow, L, pRho, pGCap] *
    Assn.list pRho (List.ofFn fun e => cappedResidual d.I T T g (d.I.m + 1) e) *
    Assn.list pGCap (List.ofFn fun e => cappedFlow g (d.I.m + 1) e) *
    (∏ j ∈ Finset.range d.I.m,
      Assn.list (pFlow + j * L) (if h : j < d.I.m then flowLimbs ⟨j, h⟩ else [])) *
    Assn.free h' (2 ^ w - h')

/-- Explicit-cost verification of `bitScale` parameterized by the costs of `tl`, `lp`, and `fin`. -/
theorem bitScale_meets {w : ℕ} {p : Program} {f tl lp fin : ℕ}
    {S : ℕ → ℕ → ℕ} {Ttl : ℕ → List (List ℕ) → ℕ}
    {Tlp : ℕ → ℕ → ℕ → ℕ} {Tfin : ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (bitScale tl lp fin))
    (htl : Meets w p tl ((topBitLengthSpec w).withCost fun x _ => Ttl x.2.2.length x.2.2))
    (hlp : Meets w p lp ((bitScaleLoopSpec w S).withCost fun d _ =>
      Tlp (bitScalingPhases d.I) d.I.n d.I.m))
    (hfin : Meets w p fin ((bitScaleFinalizeSpec w).withCost fun d _ => Tfin d.m d.L)) :
    Meets w p f ((bitScaleSpec w S).withCost fun d _ =>
      let T := bitScalingPhases d.I
      let L := T / d.k + 2
      Ttl d.I.m d.capLimbs +
        Tlp T d.I.n d.I.m +
        Tfin d.I.m L + 180) := by
  sep_enter ⟨I, k, capPtrs, capLimbs, ⟨pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens⟩, outBuf⟩ with
    hout hptrs hlimbs hcaps hk h2kw hkw hm_lt hw hn hcostB hcostW hspace
  set T := bitScalingPhases I
  set L := T / k + 2
  set stepS := 2 + 12 * I.m + S (I.n + 1) (2 * I.m)
  have hspace' : h + (5 + 2 * I.m + 3 * I.m * L + T * stepS) < 2 ^ w := hspace
  have hC_all : ∀ l ∈ capLimbs, CanonicalLimbs k l ∧ l.length * k < 2 ^ w := by
    intro l hl
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    have hj' : j < I.m := by omega
    have hc := hcaps j hj'
    rw [List.getD_eq_getElem _ _ hj] at hc
    exact ⟨hc.1, hc.2.1⟩
  have hcaps_limb : ∀ j (hj : j < I.m), Limbs k (capLimbs.getD j []) ∧
      Nat.ofDigits (2 ^ k) (capLimbs.getD j []) = I.capacity ⟨j, hj⟩ :=
    fun j hj => ⟨(hcaps j hj).1.1, (hcaps j hj).2.2⟩
  have hT_eq : Nat.size (maxLimbsVal k capLimbs) = T := by
    unfold T bitScalingPhases
    rw [maxLimbsVal_eq_circMaxCapacity hlimbs (fun j hj => (hcaps j hj).2.2)]
  sep_apply bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens
  sep_step; sep_step; sep_step; sep_step
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hm hk_1 hpCapPtrs_1 hpCapLens_1
  subst m k_1 pCapPtrs_1 pCapLens_1
  have htl_len_eq : I.m = capLimbs.length := hlimbs.symm
  sep_step from (k, capPtrs, capLimbs)
  rw [hT_eq] at hT_1
  subst T_1
  sep_apply (bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens).symm
  have hL_lt : T / k + 2 < 2 ^ w := by
    have hdiv_le : T / k ≤ T := Nat.div_le_self T k
    by_cases hT0 : T = 0
    · rw [hT0]; simp; omega
    · have hstep_ge2 : 2 ≤ stepS := by dsimp only [stepS]; omega
      have hmul : 2 * T ≤ T * stepS := by
        calc 2 * T = T * 2 := Nat.mul_comm 2 T
          _ ≤ T * stepS := Nat.mul_le_mul_left T hstep_ge2
      omega
  have hmL_lt : I.m * L < 2 ^ w := by
    have : I.m * L ≤ 3 * I.m * L := by nlinarith
    omega
  have h3mL : 3 * (I.m * L) = 3 * I.m * L := by ring
  have h2mL_lt : 2 * (I.m * L) < 2 ^ w := by omega
  have h3mL_lt : 3 * (I.m * L) < 2 ^ w := by omega
  sep_step -- L
  change L_1 = L at hL_1
  subst L_1
  sep_step -- pRho
  sep_step -- pGCap
  subst pGCap
  sep_step -- pFlow
  subst pFlow
  sep_step -- mL
  subst mL
  sep_step -- pPosAcc
  subst pPosAcc
  sep_step -- pNegAcc
  subst pNegAcc
  sep_step -- pState
  subst pState
  sep_step -- curH
  subst curH
  sep_apply split_free_initial (h := h) (m := I.m) (L := L) (w := w) (by omega)
  generalize hF_init :
    (bitScaleInput I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens *
     Assn.list h (List.replicate I.m 0) *
     Assn.list (h + I.m) (List.replicate I.m 0) *
     (∏ j ∈ Finset.range I.m, Assn.list (h + 2 * I.m + j * L) (List.replicate L 0)) *
     (∏ j ∈ Finset.range I.m, Assn.list (h + 2 * I.m + I.m * L + j * L) (List.replicate L 0)) *
     (∏ j ∈ Finset.range I.m, Assn.list (h + 2 * I.m + 2 * (I.m * L) + j * L) (List.replicate L 0)) *
     Assn.free (h + 2 * I.m + 3 * (I.m * L) + 5) (2 ^ w - (h + 2 * I.m + 3 * (I.m * L) + 5))) = Finit
  sep_apply hF_init
  sep_apply list_split_four (p := pOut) hout
  sep_step; sep_step; sep_step; sep_step
  sep_apply list_join_four pOut (h + 2 * I.m) L h (h + I.m)
  sep_apply list_split_five_zero (h + 2 * I.m + 3 * (I.m * L))
  sep_step; sep_step; sep_step; sep_step; sep_step
  sep_apply list_join_five (h + 2 * I.m + 3 * (I.m * L))
    h (h + I.m) (h + 2 * I.m + I.m * L) (h + 2 * I.m + 2 * (I.m * L)) L
  subst Finit
  sep_norm
  -- Call `bitScaleLoop`
  have hpPos_fit : h + 2 * I.m + I.m * L + I.m * L ≤ 2 ^ w := by omega
  have hpNeg_fit : h + 2 * I.m + 2 * (I.m * L) + I.m * L ≤ 2 ^ w := by omega
  have hcur_fit : h + 2 * I.m + 3 * (I.m * L) + 5 + T * stepS < 2 ^ w := by omega
  generalize hF_lp :
    (Assn.list pOut [h + 2 * I.m, L, h, h + I.m] *
     ∏ j ∈ Finset.range I.m, Assn.list (h + 2 * I.m + j * L) (List.replicate L 0)) = Flp
  sep_apply hF_lp
  sep_step from (⟨I, k, capPtrs, capLimbs, ⟨pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens⟩,
    h, h + I.m, h + 2 * I.m + I.m * L, h + 2 * I.m + 2 * (I.m * L)⟩ : BitScaleLoopData) with
    hcur_ge hcur_le hg_I_opt hacc_len hacc_bd hacc_diff hacc_val
  subst Flp
  sep_norm
  -- Prepare preconditions for `bitScaleFinalize`
  have hfin_len : ∀ e : Fin I.m, (posAcc e).length = L ∧ (negAcc e).length = L ∧
      (List.replicate L 0).length = L := fun e =>
    ⟨(hacc_len e).1, (hacc_len e).2, List.length_replicate⟩
  have hfin_half : ∀ e : Fin I.m,
      (∀ x ∈ posAcc e, x < 2 ^ (w - 1)) ∧ (∀ x ∈ negAcc e, x < 2 ^ (w - 1)) := by
    intro e
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have hjL : j < L := by rw [← (hfin_len e).1]; exact hj
      have h1 := (hacc_bd e j hjL).1
      rw [List.getD_eq_getElem _ _ hj] at h1
      exact lt_of_le_of_lt h1 (accTouches_limb_lt_half_word hk hkw)
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have hjL : j < L := by rw [← (hfin_len e).2.1]; exact hj
      have h1 := (hacc_bd e j hjL).2
      rw [List.getD_eq_getElem _ _ hj] at h1
      exact lt_of_le_of_lt h1 (accTouches_limb_lt_half_word hk hkw)
  have hval_lt_pow : ∀ e : Fin I.m,
      Nat.ofDigits (2 ^ k) (posAcc e) < (2 ^ k) ^ L ∧
      Nat.ofDigits (2 ^ k) (negAcc e) < (2 ^ k) ^ L := by
    intro e
    have hlt := bitScale_acc_lt_pow_L (T := T) hk hm_lt
    exact ⟨lt_of_le_of_lt (hacc_val e).1 hlt, lt_of_le_of_lt (hacc_val e).2 hlt⟩
  have hg_diff0 : ∀ e : Fin I.m, 0 ≤ g e ∧
      ((Nat.ofDigits (2 ^ k) (posAcc e) : ℕ) : ℤ) -
        ((Nat.ofDigits (2 ^ k) (negAcc e) : ℕ) : ℤ) = g e := fun e =>
    ⟨(Int.cast_nonneg_iff (R := ℝ)).mp (hg_I_opt.1.2 e).1, hacc_diff e⟩
  have hflow_init_eq : (∏ j ∈ Finset.range I.m,
        Assn.list (h + 2 * I.m + j * L) (List.replicate L 0)) =
      (∏ j ∈ Finset.range I.m,
        Assn.list (h + 2 * I.m + j * L) (if _ : j < I.m then List.replicate L 0 else [])) := by
    refine Finset.prod_congr rfl fun j hj => by simp [Finset.mem_range.mp hj]
  sep_apply hflow_init_eq
  have hL_pos : 0 < L := Nat.succ_pos _
  have hpFlow_fit : h + 2 * I.m + I.m * L ≤ 2 ^ w := by omega
  generalize hF_fin :
    (bitScaleInput I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens *
     Assn.list pOut [h + 2 * I.m, L, h, h + I.m] *
     Assn.list (h + 2 * I.m + 3 * (I.m * L))
       [h, h + I.m, h + 2 * I.m + I.m * L, h + 2 * I.m + 2 * (I.m * L), L] *
     Assn.list h (List.ofFn fun e => cappedResidual I T T g (I.m + 1) e) *
     Assn.list (h + I.m) (List.ofFn fun e => cappedFlow g (I.m + 1) e) *
     Assn.free curH (2 ^ w - curH)) = Ffin
  sep_apply hF_fin
  sep_step from (⟨I.m, k, L, g, posAcc, negAcc, fun _ => List.replicate L 0⟩ : BitScaleFinalizeData) with
    hflow_post
  subst Ffin
  sep_norm
  have hflow_spec : ∀ e : Fin I.m, 0 ≤ g e ∧ Limbs k (finalizedFlowLimbs k posAcc negAcc e) ∧
      (finalizedFlowLimbs k posAcc negAcc e).length = L ∧
      ((Nat.ofDigits (2 ^ k) (finalizedFlowLimbs k posAcc negAcc e) : ℕ) : ℤ) = g e := fun e =>
    ⟨(hg_diff0 e).1, hflow_post e⟩
  have hres_pos : ∀ e : Fin I.m,
      (0 < cappedResidual I T T g (I.m + 1) e ↔
        0 < (I.residual g).capacity (Fin.castAdd I.m e)) ∧
      (0 < cappedFlow g (I.m + 1) e ↔
        0 < (I.residual g).capacity (Fin.natAdd I.m e)) :=
    fun e => residual_pos_iff_of_capped I T g e
  have hcur_ge_h : h ≤ curH := by omega
  have h3mL_unfold : 3 * (I.m * L) = 3 * I.m * (bitScalingPhases I / k + 2) := by
    dsimp only [L, T]; ring
  have hcur_le_space : curH ≤ h + bitScaleSpace I k S := by dsimp only [bitScaleSpace]; omega
  have hTtl_eq : Ttl capLimbs.length capLimbs = Ttl I.m capLimbs := by rw [hlimbs]
  rw [hTtl_eq]
  sep_step -- return curH
  dsimp only [T]; omega

/-! ### Direct concrete-cost and `MeetsO` theorems from `solverContract` -/

/-- Explicit-cost Stage 2 theorem when all internal helpers are the concrete `NarrowProg`
procedures and `sol` meets `solverContract w Tsol S`. -/
theorem bitScale_meets_direct {w : ℕ} {p : Program}
    {f bl tl lb acc norm sub fwd rev pw nzl clmp edge pu mx lp fin sol : ℕ}
    {Tsol S : ℕ → ℕ → ℕ} {solBody : Stmt}
    (hp : p.procs[f]? = some (bitScale tl lp fin))
    (hbl : p.procs[bl]? = some bitLength)
    (htl : p.procs[tl]? = some (topBitLength bl))
    (hlb : p.procs[lb]? = some limbBit)
    (hacc : p.procs[acc]? = some accAdd)
    (hnorm : p.procs[norm]? = some accNormalize)
    (hsub : p.procs[sub]? = some limbsSub)
    (hfwd : p.procs[fwd]? = some (phaseWriteFwd lb))
    (hrev : p.procs[rev]? = some phaseWriteRev)
    (hpw : p.procs[pw]? = some (phaseWrite fwd rev))
    (hnzl : p.procs[nzl]? = some nzLoad)
    (hclmp : p.procs[clmp]? = some clamp)
    (hedge : p.procs[edge]? = some (phaseUpdateEdge lb acc nzl clmp))
    (hpu : p.procs[pu]? = some (phaseUpdate edge))
    (hmx : p.procs[mx]? = some max2)
    (hlp : p.procs[lp]? = some (bitScaleLoop pw sol pu mx))
    (hfin : p.procs[fin]? = some (bitScaleFinalize norm sub))
    (hsolC : MeetsContract w p sol (solverContract w Tsol S))
    (hsolP : p.procs[sol]? = some solBody) :
    Meets w p f ((bitScaleSpec w S).withCost fun d _ =>
      let T := bitScalingPhases d.I
      T * Tsol (d.I.n + 1) (2 * d.I.m) +
        720 * T * d.I.m + 525 * T + 150 * d.I.m * (T / d.k + 2) + 215 * d.I.m + 360) := by
  have htlM := topBitLength_meets (w := w) htl (bitLength_meets (w := w) hbl)
  have hpwM := phaseWrite_meets_direct (w := w) hpw hfwd hrev hlb
  have hsolM := solverContract_meets_solverSpec hsolC hsolP
  have hpuM := phaseUpdate_meets_direct (w := w) hpu hedge
    (limbBit_meets (w := w) hlb) (accAdd_meets (w := w) hacc) hnzl hclmp
  have hmxM := max2_meets (w := w) hmx
  have hlpM := bitScaleLoop_meets (w := w) (S := S)
    (Tpw := fun m => 285 * m + 290) (Tsol := Tsol)
    (Tpu := fun m => (35 + 2 * 70 + 260) * m + 120)
    hlp hpwM hsolM hpuM hmxM
  have hfinM := bitScaleFinalize_meets_direct (w := w) hfin hnorm hsub
  have hmain := bitScale_meets (w := w) (S := S)
    (Ttl := fun m xs => 75 * m + (12 * Nat.size (maxTopLimb xs) + 10) + 50)
    (Tlp := fun T n m => T *
      (285 * m + 290 + Tsol (n + 1) (2 * m) +
        ((35 + 2 * 70 + 260) * m + 120) + 100) + 80)
    (Tfin := fun m L => (150 * L + 140) * m + 40)
    hp htlM hlpM hfinM
  refine hmain.withCost_mono_on
    (P := fun d _ => 1 ≤ d.k ∧ d.capLimbs.length = d.I.m ∧
      (∀ j (hj : j < d.I.m), CanonicalLimbs d.k (d.capLimbs.getD j []) ∧
        (d.capLimbs.getD j []).length * d.k < 2 ^ w ∧
        Nat.ofDigits (2 ^ d.k) (d.capLimbs.getD j []) = d.I.capacity ⟨j, hj⟩)) ?_ ?_
  · intro d args h c hx
    simp only [bitScaleSpec] at hx
    obtain ⟨pIn, hx⟩ := (Assn.iSup_apply _ _ _).mp hx
    obtain ⟨pOut, hx⟩ := (Assn.iSup_apply _ _ _).mp hx
    obtain ⟨h0, hx⟩ := (Assn.iSup_apply _ _ _).mp hx
    rw [mul_assoc, mul_assoc] at hx
    obtain ⟨hpure, _⟩ := Assn.pure_mul_apply.mp hx
    exact ⟨Heap.empty, h, 0, c, Heap.disjoint_empty_left _, (Heap.empty_union _).symm,
      (zero_add _).symm, ⟨⟨hpure.2.2.2.2.2.1, hpure.2.2.2.1, hpure.2.2.2.2.1⟩, rfl, rfl⟩, trivial⟩
  · intro d _ ⟨hk, hlen, hcaps⟩
    have hC : ∀ l ∈ d.capLimbs, CanonicalLimbs d.k l ∧ l.length * d.k < 2 ^ w := by
      intro l hl
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
      have hj' : j < d.I.m := by omega
      have hc := hcaps j hj'
      rw [List.getD_eq_getElem _ _ hj] at hc
      exact ⟨hc.1, hc.2.1⟩
    have htop := size_maxTopLimb_le_bitScalingPhases hk hlen hC (fun j hj => (hcaps j hj).2.2)
    dsimp only
    nlinarith

/-- Big-O specification of Stage 2:
`T * T_sol (n + 1) (2 * m) + O(T * m + m * (T / k + 1) + T + 1)`. -/
theorem bitScale_meetsO {w : ℕ} {p : Program}
    {f bl tl lb acc norm sub fwd rev pw nzl clmp edge pu mx lp fin sol : ℕ}
    {Tsol S : ℕ → ℕ → ℕ} {solBody : Stmt}
    (hp : p.procs[f]? = some (bitScale tl lp fin))
    (hbl : p.procs[bl]? = some bitLength)
    (htl : p.procs[tl]? = some (topBitLength bl))
    (hlb : p.procs[lb]? = some limbBit)
    (hacc : p.procs[acc]? = some accAdd)
    (hnorm : p.procs[norm]? = some accNormalize)
    (hsub : p.procs[sub]? = some limbsSub)
    (hfwd : p.procs[fwd]? = some (phaseWriteFwd lb))
    (hrev : p.procs[rev]? = some phaseWriteRev)
    (hpw : p.procs[pw]? = some (phaseWrite fwd rev))
    (hnzl : p.procs[nzl]? = some nzLoad)
    (hclmp : p.procs[clmp]? = some clamp)
    (hedge : p.procs[edge]? = some (phaseUpdateEdge lb acc nzl clmp))
    (hpu : p.procs[pu]? = some (phaseUpdate edge))
    (hmx : p.procs[mx]? = some max2)
    (hlp : p.procs[lp]? = some (bitScaleLoop pw sol pu mx))
    (hfin : p.procs[fin]? = some (bitScaleFinalize norm sub))
    (hsolC : MeetsContract w p sol (solverContract w Tsol S))
    (hsolP : p.procs[sol]? = some solBody) :
    MeetsO w p f (bitScaleSpec w S) fun d _ =>
      let T := bitScalingPhases d.I
      T * Tsol (d.I.n + 1) (2 * d.I.m) + T * d.I.m + d.I.m * (T / d.k + 1) + T + 1 := by
  refine MeetsO.of_meets
    (bitScale_meets_direct hp hbl htl hlb hacc hnorm hsub hfwd hrev hpw hnzl hclmp hedge hpu hmx
      hlp hfin hsolC hsolP)
    ⟨720, fun ⟨d, _⟩ => ?_⟩
  dsimp only
  have hm_le : d.I.m ≤ d.I.m * (bitScalingPhases d.I / d.k + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  nlinarith

/-! ### Polymorphic module -/

/-- Procedure names for `bitScaleMod`, polymorphic over any name type `ι`. -/
structure BitScaleNames (ι : Type) where
  bitScale : ι
  bitLength : ι
  topBitLength : ι
  limbBit : ι
  accAdd : ι
  accNormalize : ι
  limbsSub : ι
  phaseWriteFwd : ι
  phaseWriteRev : ι
  phaseWrite : ι
  nzLoad : ι
  clamp : ι
  phaseUpdateEdge : ι
  phaseUpdate : ι
  max2 : ι
  bitScaleLoop : ι
  bitScaleFinalize : ι
  solver : ι

/-- Self-contained polymorphic module for Stage 2 (`bitScale` and all of its internal callees),
calling the external circulation solver at `names.solver`. -/
def bitScaleMod {ι : Type} (names : BitScaleNames ι) : Module ι :=
  ⟨[(names.bitLength, fun _ => bitLength),
    (names.topBitLength, fun idx => topBitLength (idx names.bitLength)),
    (names.limbBit, fun _ => limbBit),
    (names.accAdd, fun _ => accAdd),
    (names.accNormalize, fun _ => accNormalize),
    (names.limbsSub, fun _ => limbsSub),
    (names.phaseWriteFwd, fun idx => phaseWriteFwd (idx names.limbBit)),
    (names.phaseWriteRev, fun _ => phaseWriteRev),
    (names.phaseWrite, fun idx => phaseWrite (idx names.phaseWriteFwd) (idx names.phaseWriteRev)),
    (names.nzLoad, fun _ => nzLoad),
    (names.clamp, fun _ => clamp),
    (names.phaseUpdateEdge, fun idx =>
      phaseUpdateEdge (idx names.limbBit) (idx names.accAdd) (idx names.nzLoad) (idx names.clamp)),
    (names.phaseUpdate, fun idx => phaseUpdate (idx names.phaseUpdateEdge)),
    (names.max2, fun _ => max2),
    (names.bitScaleLoop, fun idx =>
      bitScaleLoop (idx names.phaseWrite) (idx names.solver) (idx names.phaseUpdate) (idx names.max2)),
    (names.bitScaleFinalize, fun idx =>
      bitScaleFinalize (idx names.accNormalize) (idx names.limbsSub)),
    (names.bitScale, fun idx =>
      bitScale (idx names.topBitLength) (idx names.bitScaleLoop) (idx names.bitScaleFinalize))]⟩

theorem bitScaleMod_noRand {ι : Type} (names : BitScaleNames ι) :
    (bitScaleMod names).NoRand := by
  wram_no_rand

/-- In any program placing `bitScaleMod names` alongside an external circulation solver meeting
`solverContract w Tsol S`, `bitScale` meets `bitScaleSpec w S` in
`O(T * Tsol (n + 1) (2 * m) + T * m + m * (T / k + 1) + T + 1)` steps. -/
theorem bitScaleMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {names : BitScaleNames ι} {Tsol S : ℕ → ℕ → ℕ} {solBody : Stmt}
    (hp : (bitScaleMod names).Placed p idx)
    (hsolC : MeetsContract w p (idx names.solver) (solverContract w Tsol S))
    (hsolP : p.procs[idx names.solver]? = some solBody) :
    MeetsO w p (idx names.bitScale) (bitScaleSpec w S) fun d _ =>
      let T := bitScalingPhases d.I
      T * Tsol (d.I.n + 1) (2 * d.I.m) + T * d.I.m + d.I.m * (T / d.k + 1) + T + 1 :=
  bitScale_meetsO
    (hp.get (n := names.bitScale) (b := fun idx =>
      bitScale (idx names.topBitLength) (idx names.bitScaleLoop) (idx names.bitScaleFinalize))
      (by simp [bitScaleMod]))
    (hp.get (n := names.bitLength) (b := fun _ => bitLength) (by simp [bitScaleMod]))
    (hp.get (n := names.topBitLength) (b := fun idx => topBitLength (idx names.bitLength))
      (by simp [bitScaleMod]))
    (hp.get (n := names.limbBit) (b := fun _ => limbBit) (by simp [bitScaleMod]))
    (hp.get (n := names.accAdd) (b := fun _ => accAdd) (by simp [bitScaleMod]))
    (hp.get (n := names.accNormalize) (b := fun _ => accNormalize) (by simp [bitScaleMod]))
    (hp.get (n := names.limbsSub) (b := fun _ => limbsSub) (by simp [bitScaleMod]))
    (hp.get (n := names.phaseWriteFwd) (b := fun idx => phaseWriteFwd (idx names.limbBit))
      (by simp [bitScaleMod]))
    (hp.get (n := names.phaseWriteRev) (b := fun _ => phaseWriteRev) (by simp [bitScaleMod]))
    (hp.get (n := names.phaseWrite) (b := fun idx =>
      phaseWrite (idx names.phaseWriteFwd) (idx names.phaseWriteRev))
      (by simp [bitScaleMod]))
    (hp.get (n := names.nzLoad) (b := fun _ => nzLoad) (by simp [bitScaleMod]))
    (hp.get (n := names.clamp) (b := fun _ => clamp) (by simp [bitScaleMod]))
    (hp.get (n := names.phaseUpdateEdge) (b := fun idx =>
      phaseUpdateEdge (idx names.limbBit) (idx names.accAdd) (idx names.nzLoad) (idx names.clamp))
      (by simp [bitScaleMod]))
    (hp.get (n := names.phaseUpdate) (b := fun idx => phaseUpdate (idx names.phaseUpdateEdge))
      (by simp [bitScaleMod]))
    (hp.get (n := names.max2) (b := fun _ => max2) (by simp [bitScaleMod]))
    (hp.get (n := names.bitScaleLoop) (b := fun idx =>
      bitScaleLoop (idx names.phaseWrite) (idx names.solver) (idx names.phaseUpdate) (idx names.max2))
      (by simp [bitScaleMod]))
    (hp.get (n := names.bitScaleFinalize) (b := fun idx =>
      bitScaleFinalize (idx names.accNormalize) (idx names.limbsSub))
      (by simp [bitScaleMod]))
    hsolC hsolP

end MinCostFlow.NarrowProg
