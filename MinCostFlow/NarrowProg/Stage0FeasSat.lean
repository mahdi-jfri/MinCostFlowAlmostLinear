module

public import MinCostFlow.NarrowProg.Stage0FeasBuild
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 4 (artificial-arc saturation check): `Stage0FeasSat`

Verifies:
1. `stage0FeasCheckOne`: checks whether a `K1`-limb flow value equals a canonical capacity limb
   list (`canonLen` + `limbsCmp`).
2. `stage0FeasSatCheck`: scans all pruned artificial arcs (`j ∈ [m1Orig, m1)`) and returns `1`
   iff every artificial arc is saturated.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Pure helper lemmas for feasibility scatter and saturation -/

private theorem cmpCode_eq_one_iff (x y : ℕ) : cmpCode x y = 1 ↔ x = y := by
  unfold cmpCode; split_ifs <;> simp <;> omega

theorem feas_positiveIndex_lt_iff (I : Instance) (hv : I.IsValid)
    (j : Fin (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m) :
    (FlowReduction.buildFeasibilityInstance I hv).positiveIndex j =
      if h : j.val < (feasOrigPos I hv I.m).length then
        Fin.castAdd (I.n + I.n) ((feasOrigPos I hv I.m)[j.val]'h)
      else
        (FlowReduction.buildFeasibilityInstance I hv).positiveIndex j := by
  split_ifs with h
  · unfold Circulation.positiveIndex
    have hpe := feas_positiveEdges_eq I hv
    rw [List.getElem_of_eq hpe j.isLt]
    rw [List.getElem_append_left (by simp only [List.length_append, List.length_map]; omega)]
    rw [List.getElem_append_left (by simp only [List.length_map]; exact h)]
    simp
  · rfl

theorem feas_positiveIndex_ge_m_iff (I : Instance) (hv : I.IsValid)
    (j : Fin (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m) :
    I.m ≤ ((FlowReduction.buildFeasibilityInstance I hv).positiveIndex j).val ↔
      (feasOrigPos I hv I.m).length ≤ j.val := by
  unfold Circulation.positiveIndex
  have hpe := feas_positiveEdges_eq I hv
  rw [List.getElem_of_eq hpe j.isLt]
  by_cases h1 : j.val < (feasOrigPos I hv I.m).length
  · rw [List.getElem_append_left (by simp only [List.length_append, List.length_map]; omega)]
    rw [List.getElem_append_left (by simp only [List.length_map]; exact h1)]
    simp only [List.getElem_map, Fin.val_castAdd]
    have hlt := ((feasOrigPos I hv I.m)[j.val]'h1).isLt
    omega
  · by_cases h2 : j.val < (feasOrigPos I hv I.m).length + (feasArtPos I I.n).length
    · rw [List.getElem_append_left (by simp only [List.length_append, List.length_map]; omega)]
      rw [List.getElem_append_right (by simp only [List.length_map]; omega)]
      simp only [List.getElem_map, Fin.val_natAdd, Fin.val_castAdd]
      omega
    · rw [List.getElem_append_right (by simp only [List.length_append, List.length_map]; omega)]
      simp only [List.getElem_map, Fin.val_natAdd]
      omega

theorem feas_scatterPositive_orig (I : Instance) (hv : I.IsValid)
    (f' : Fin (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m → ℤ)
    (j : ℕ) (hj : j < (feasOrigPos I hv I.m).length) :
    let P := FlowReduction.buildFeasibilityInstance I hv
    let hj' : j < P.withoutZeroEdges.m := by
      have hm := feas_m_eq I hv; change P.withoutZeroEdges.m = _ at hm; omega
    P.scatterPositive f' (Fin.castAdd (I.n + I.n) ((feasOrigPos I hv I.m)[j]'hj)) = f' ⟨j, hj'⟩ := by
  intro P hj'
  have hreal : ((P.scatterPositive f'
      (Fin.castAdd (I.n + I.n) ((feasOrigPos I hv I.m)[j]'hj)) : ℤ) : ℝ) = (f' ⟨j, hj'⟩ : ℝ) := by
    have h1 := congrFun (P.scatterPositive_cast f')
      (Fin.castAdd (I.n + I.n) ((feasOrigPos I hv I.m)[j]'hj))
    have h2 := congrFun (P.scatterPositive_eq_extendPositive (fun e => (f' e : ℝ)))
      (Fin.castAdd (I.n + I.n) ((feasOrigPos I hv I.m)[j]'hj))
    rw [h1, h2]
    have hidx : P.positiveIndex ⟨j, hj'⟩ = Fin.castAdd (I.n + I.n) ((feasOrigPos I hv I.m)[j]'hj) := by
      have := feas_positiveIndex_lt_iff I hv ⟨j, hj'⟩
      simpa only [hj, ↓reduceDIte] using this
    rw [← hidx]
    have hpos : 0 < P.capacity (P.positiveIndex ⟨j, hj'⟩) :=
      (P.mem_positiveEdges_iff _).mp (List.getElem_mem hj')
    rw [Circulation.extendPositive, dite_eq_left hpos, P.positiveSlot_positiveIndex ⟨j, hj'⟩ hpos]
  exact_mod_cast hreal

theorem feas_scatterPositive_not_orig (I : Instance) (hv : I.IsValid)
    (f' : Fin (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m → ℤ)
    (e : Fin I.m) (hne : e ∉ feasOrigPos I hv I.m) :
    (FlowReduction.buildFeasibilityInstance I hv).scatterPositive f' (Fin.castAdd (I.n + I.n) e) = 0 := by
  let P := FlowReduction.buildFeasibilityInstance I hv
  have hcap0 : P.capacity (Fin.castAdd (I.n + I.n) e) = 0 := by
    by_contra hne0
    have hpos : 0 < (FlowReduction.shiftedGraph I hv).capacity e := by
      have : P.capacity (Fin.castAdd (I.n + I.n) e) = (FlowReduction.shiftedGraph I hv).capacity e := by
        simp [P, Fin.addCases_left]
      omega
    apply hne
    unfold feasOrigPos
    rw [List.take_of_length_le (by simp)]
    exact List.mem_filter.mpr ⟨List.mem_finRange e, decide_eq_true_eq.mpr hpos⟩
  have hreal : ((P.scatterPositive f' (Fin.castAdd (I.n + I.n) e) : ℤ) : ℝ) = 0 := by
    have h1 := congrFun (P.scatterPositive_cast f') (Fin.castAdd (I.n + I.n) e)
    have h2 := congrFun (P.scatterPositive_eq_extendPositive (fun r => (f' r : ℝ)))
      (Fin.castAdd (I.n + I.n) e)
    rw [h1, h2, P.extendPositive_zero _ _ hcap0]
  exact_mod_cast hreal

/-! ### `stage0FeasCheckOne`: check equality of one `K1`-limb flow entry with canonical capacity -/

wram_def stage0FeasCheckOne (cLen lCmp : ℕ) (pCapPtr, cLenE, pFlowE, K1) {
  tLen := cLen(pFlowE, K1)
  if tLen == cLenE {
    cmp := lCmp(pFlowE, pCapPtr, tLen)
    if cmp == 1 {
      return 1
    } else {
      return 0
    }
  } else {
    return 0
  }
}

structure FeasCheckOneData where
  k : ℕ
  capLimb : List ℕ
  flowLimb : List ℕ

def stage0FeasCheckOneSpec : Spec FeasCheckOneData where
  pre := fun d args => ⨆ (pCapPtr : ℕ) (pFlowE : ℕ),
    ⌜args = [pCapPtr, d.capLimb.length, pFlowE, d.flowLimb.length] ∧
      1 ≤ d.k ∧ CanonicalLimbs d.k d.capLimb ∧ Limbs d.k d.flowLimb⌝ *
    Assn.list pCapPtr d.capLimb * Assn.list pFlowE d.flowLimb
  post := fun d args v => ⨆ (pCapPtr : ℕ) (pFlowE : ℕ),
    ⌜args = [pCapPtr, d.capLimb.length, pFlowE, d.flowLimb.length] ∧ v ≤ 1 ∧
      (v = 1 ↔ Nat.ofDigits (2 ^ d.k) d.flowLimb = Nat.ofDigits (2 ^ d.k) d.capLimb)⌝ *
    Assn.list pCapPtr d.capLimb * Assn.list pFlowE d.flowLimb

theorem stage0FeasCheckOne_meets {w : ℕ} {p : Program} {f cLen lCmp : ℕ}
    {Tcan Tcmp : ℕ → ℕ} (hw : 2 < 2 ^ w)
    (hTcmp_mono : ∀ a b, a ≤ b → Tcmp a ≤ Tcmp b)
    (hp : p.procs[f]? = some (stage0FeasCheckOne cLen lCmp))
    (hcan : Meets w p cLen (canonLenSpec.withCost fun x _ => Tcan x.2.length))
    (hcmp : Meets w p lCmp (limbsCmpSpec.withCost fun x _ => Tcmp x.2.1.length)) :
    Meets w p f (stage0FeasCheckOneSpec.withCost fun d _ =>
      Tcan d.flowLimb.length + Tcmp d.flowLimb.length + 50) := by
  sep_enter d with hk1 hcanCap hlimFlow
  set dig := Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) d.flowLimb)
  have hcap_dig : d.capLimb = Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) d.capLimb) := by
    exact canonical_eq_digits hk1 hcanCap
  sep_step from (d.k, d.flowLimb) with hpad
  have hdig_le : dig.length ≤ d.flowLimb.length := by
    have := congrArg List.length hpad
    simp only [padLimbs, List.length_append, List.length_replicate] at this
    dsimp only [dig]; omega
  sep_step
  · have hlen_eq : dig.length = d.capLimb.length := by dsimp only [dig]; omega
    have hsplit : Assn.list pFlowE d.flowLimb =
        Assn.list pFlowE dig *
        Assn.list (pFlowE + dig.length) (List.replicate (d.flowLimb.length - dig.length) 0) := by
      conv_lhs => rw [hpad]
      rw [padLimbs, Assn.list_append]
    sep_apply hsplit
    have hTle : Tcmp dig.length ≤ Tcmp d.flowLimb.length := hTcmp_mono _ _ hdig_le
    have hdig_lim : Limbs d.k dig := digits_limbs hk1 _
    have hcap_lim : Limbs d.k d.capLimb := hcanCap.1
    sep_step from (d.k, dig, d.capLimb)
    sep_apply hsplit.symm
    have hof : Nat.ofDigits (2 ^ d.k) dig = Nat.ofDigits (2 ^ d.k) d.flowLimb :=
      Nat.ofDigits_digits (2 ^ d.k) _
    sep_step
    · sep_step
      · simp [hcmp_1, cmpCode_eq_one_iff, hof] at hcond_1
        simp [hcond_1]
    · sep_step
      · simp [hcmp_1, cmpCode_eq_one_iff, hof] at hcond_1
        simp [hcond_1]
  · sep_step
    · simp only [Nat.zero_ne_one, false_iff]
      intro hEq
      have hlen : dig.length = d.capLimb.length := by
        rw [hcap_dig]; simp only [dig, hEq]
      dsimp only [dig] at hlen
      omega

/-! ### `stage0FeasSatCheck`: verify all artificial arcs `[m1Orig, m1)` are saturated -/

wram_def stage0FeasSatCheck (checkOne : ℕ)
    (m1Orig, m1, pCapPtr1, pCapLen1, pFlow1, K1) {
  ok := 1
  off := m1Orig * K1
  j := m1Orig
  for t in 0 .. (m1 - m1Orig) {
    if ok == 1 {
      ok := checkOne(mem[pCapPtr1 + j], mem[pCapLen1 + j], pFlow1 + off, K1)
    }
    off := off + K1
    j := j + 1
  }
  return ok
}

structure FeasSatCheckData where
  k : ℕ
  m1Orig : ℕ
  m1 : ℕ
  K1 : ℕ
  capPtrs : List ℕ
  capLimbs : List (List ℕ)
  flowLimbs : Fin m1 → List ℕ

def stage0FeasSatCheckSpec (w : ℕ) : Spec FeasSatCheckData where
  pre := fun d args => ⨆ (pCapPtr1 : ℕ) (pCapLen1 : ℕ) (pFlow1 : ℕ),
    ⌜args = [d.m1Orig, d.m1, pCapPtr1, pCapLen1, pFlow1, d.K1] ∧
      1 ≤ d.k ∧ d.m1Orig ≤ d.m1 ∧
      d.capPtrs.length = d.m1 ∧ d.capLimbs.length = d.m1 ∧
      (∀ j (_hj : j < d.m1), CanonicalLimbs d.k (d.capLimbs.getD j [])) ∧
      (∀ j : Fin d.m1, Limbs d.k (d.flowLimbs j) ∧ (d.flowLimbs j).length = d.K1) ∧
      pCapPtr1 + d.m1 ≤ 2 ^ w ∧ pCapLen1 + d.m1 ≤ 2 ^ w ∧
      d.m1 * d.K1 < 2 ^ w ∧ d.m1 < 2 ^ w ∧ d.K1 < 2 ^ w⌝ *
    Assn.list pCapPtr1 d.capPtrs *
    Assn.list pCapLen1 (d.capLimbs.map List.length) *
    (∏ j ∈ Finset.range d.m1, Assn.list (d.capPtrs.getD j 0) (d.capLimbs.getD j [])) *
    (∏ j ∈ Finset.range d.m1,
      Assn.list (pFlow1 + j * d.K1) (if h : j < d.m1 then d.flowLimbs ⟨j, h⟩ else []))
  post := fun d args ok => ⨆ (pCapPtr1 : ℕ) (pCapLen1 : ℕ) (pFlow1 : ℕ),
    ⌜args = [d.m1Orig, d.m1, pCapPtr1, pCapLen1, pFlow1, d.K1] ∧ ok ≤ 1 ∧
      (ok = 1 ↔ ∀ j : Fin d.m1, d.m1Orig ≤ j.val →
        Nat.ofDigits (2 ^ d.k) (d.flowLimbs j) =
          Nat.ofDigits (2 ^ d.k) (d.capLimbs.getD j.val []))⌝ *
    Assn.list pCapPtr1 d.capPtrs *
    Assn.list pCapLen1 (d.capLimbs.map List.length) *
    (∏ j ∈ Finset.range d.m1, Assn.list (d.capPtrs.getD j 0) (d.capLimbs.getD j [])) *
    (∏ j ∈ Finset.range d.m1,
      Assn.list (pFlow1 + j * d.K1) (if h : j < d.m1 then d.flowLimbs ⟨j, h⟩ else []))

theorem stage0FeasSatCheck_meets {w : ℕ} {p : Program} {f checkOne : ℕ}
    {Tchk : ℕ → ℕ} (hw : 2 < 2 ^ w)
    (hp : p.procs[f]? = some (stage0FeasSatCheck checkOne))
    (hchk : Meets w p checkOne (stage0FeasCheckOneSpec.withCost fun x _ => Tchk x.flowLimb.length)) :
    Meets w p f ((stage0FeasSatCheckSpec w).withCost fun d _ =>
      (Tchk d.K1 + 75) * (d.m1 - d.m1Orig) + 45) := by
  sep_enter d with hk1 hle hcpLen hclLen hcanCap hfl hpCP hpCL hmK hmW hKW
  have hm0K : d.m1Orig * d.K1 < 2 ^ w :=
    lt_of_le_of_lt (Nat.mul_le_mul_right d.K1 hle) hmK
  sep_step; sep_step; sep_step
  sep_for (fun t (ok : ℕ) => (⟨[d.m1Orig, d.m1, pCapPtr1, pCapLen1, pFlow1, d.K1,
      ok, (d.m1Orig + t) * d.K1, d.m1Orig + t, t],
      t ≤ d.m1 - d.m1Orig ∧ ok ≤ 1 ∧
      (ok = 1 ↔ ∀ r (_hr : r < t) (hrm : d.m1Orig + r < d.m1),
        Nat.ofDigits (2 ^ d.k) (d.flowLimbs ⟨d.m1Orig + r, hrm⟩) =
          Nat.ofDigits (2 ^ d.k) (d.capLimbs.getD (d.m1Orig + r) [])),
      (Tchk d.K1 + 60) * (d.m1 - d.m1Orig - t) + 15,
      [Assn.list pCapPtr1 d.capPtrs,
       Assn.list pCapLen1 (d.capLimbs.map List.length),
       ∏ r ∈ Finset.range d.m1, Assn.list (d.capPtrs.getD r 0) (d.capLimbs.getD r []),
       ∏ r ∈ Finset.range d.m1,
         Assn.list (pFlow1 + r * d.K1) (if h : r < d.m1 then d.flowLimbs ⟨r, h⟩ else [])]⟩ : SInv))
    with ok
  · have hok_le : ok ≤ 1 := hinv_1
    have hok_iff := hinv_2
    have hj_lt : d.m1Orig + t < d.m1 := by omega
    have hj_mem : d.m1Orig + t ∈ Finset.range d.m1 := Finset.mem_range.mpr hj_lt
    have hmul_next : (d.m1Orig + t) * d.K1 + d.K1 = (d.m1Orig + (t + 1)) * d.K1 := by ring
    have hmul_lt : (d.m1Orig + (t + 1)) * d.K1 < 2 ^ w :=
      lt_of_le_of_lt (Nat.mul_le_mul_right d.K1 (by omega)) hmK
    sep_step
    · -- ok == 1 branch
      have hcapPtr_get : d.capPtrs[d.m1Orig + t]'(by omega) = d.capPtrs.getD (d.m1Orig + t) 0 := by
        rw [List.getD_eq_getElem _ _ (by omega)]
      have hcapLen_get : (d.capLimbs.map List.length)[d.m1Orig + t]'(by simp [hclLen]; exact hj_lt) =
          (d.capLimbs.getD (d.m1Orig + t) []).length := by
        rw [List.getElem_map, List.getD_eq_getElem _ _ (by omega)]
      have hspCap : (∏ r ∈ Finset.range d.m1, Assn.list (d.capPtrs.getD r 0) (d.capLimbs.getD r [])) =
          Assn.list (d.capPtrs.getD (d.m1Orig + t) 0) (d.capLimbs.getD (d.m1Orig + t) []) *
          (∏ r ∈ (Finset.range d.m1).erase (d.m1Orig + t),
            Assn.list (d.capPtrs.getD r 0) (d.capLimbs.getD r [])) :=
        (Finset.mul_prod_erase _ _ hj_mem).symm
      have hspFl : (∏ r ∈ Finset.range d.m1,
          Assn.list (pFlow1 + r * d.K1) (if h : r < d.m1 then d.flowLimbs ⟨r, h⟩ else [])) =
          Assn.list (pFlow1 + (d.m1Orig + t) * d.K1) (d.flowLimbs ⟨d.m1Orig + t, hj_lt⟩) *
          (∏ r ∈ (Finset.range d.m1).erase (d.m1Orig + t),
            Assn.list (pFlow1 + r * d.K1) (if h : r < d.m1 then d.flowLimbs ⟨r, h⟩ else [])) := by
        rw [← Finset.mul_prod_erase _ _ hj_mem, dite_eq_left hj_lt]
      sep_apply hspCap
      sep_apply hspFl
      let cd : FeasCheckOneData := ⟨d.k, d.capLimbs.getD (d.m1Orig + t) [], d.flowLimbs ⟨d.m1Orig + t, hj_lt⟩⟩
      have hlen_fl : cd.flowLimb.length = d.K1 := (hfl ⟨d.m1Orig + t, hj_lt⟩).2
      have hcan_cur : CanonicalLimbs cd.k cd.capLimb := hcanCap (d.m1Orig + t) hj_lt
      have hlim_cur : Limbs cd.k cd.flowLimb := (hfl ⟨d.m1Orig + t, hj_lt⟩).1
      sep_step from cd with _ _ hveq_le hveq_iff
      · sep_apply hspCap.symm
        sep_apply hspFl.symm
        sep_step; sep_step
        · rw [hlen_fl]; push_cast; ring_nf; omega
        · constructor
          · intro hv1 r hr hrm
            by_cases hrt : r < t
            · exact hok_iff.mp hcond r hrt hrm
            · have hreq : r = t := by omega
              subst hreq
              exact hveq_iff.mp hv1
          · intro hall
            exact hveq_iff.mpr (hall t (by omega) hj_lt)
      · by_cases hK0 : d.K1 = 0
        · rw [hK0, mul_zero, add_zero]; omega
        · dsimp only [cd] at hlen_fl; omega
    · -- ok != 1 branch (ok = 0)
      sep_step; sep_step; sep_step
      · exact ⟨fun h1 => absurd h1 hcond,
          fun hall => absurd (hok_iff.mpr fun r hr hrm => hall r (by omega) hrm) hcond⟩
  · have hok_le : ok ≤ 1 := hinv_1
    have hok_iff := hinv_2
    sep_step
    · rw [hok_iff]
      constructor
      · intro hall j hj
        have hr : j.val - d.m1Orig < d.m1 - d.m1Orig := by omega
        have hrm : d.m1Orig + (j.val - d.m1Orig) < d.m1 := by omega
        have heq := hall (j.val - d.m1Orig) hr hrm
        have hidx : d.m1Orig + (j.val - d.m1Orig) = j.val := by omega
        simpa only [hidx] using heq
      · intro hall r hr hrm
        exact hall ⟨d.m1Orig + r, hrm⟩ (Nat.le_add_right d.m1Orig r)

end MinCostFlow.NarrowProg
