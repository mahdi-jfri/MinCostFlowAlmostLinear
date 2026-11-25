module

public import WordRAM.Module
public import MinCostFlow.NarrowProg.Stage0CheckHelpers
public import MinCostFlow.Scaling.IsolatedDemands
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring

/-!
# Stage 0, item 2: capacity check, endpoint labels, isolated check, and `L_dem` (`stage0Check`)

Implements and verifies:
- `stage0IsoCheck`: verifies that every unlabeled (isolated) vertex has demand length `0`
  (equivalent to `FlowReduction.isolatedCheck I hv = true`);
- `stage0MaxLen`: computes `L_dem = 1 + max` of all edge `lower`/`upper` limb lengths and active
  vertex demand limb lengths, giving `1 ≤ L_dem ≤ narrowMaxCapLimbs I + 1`;
- `stage0Check`: runs `stage0CheckCaps`, `stage0Labels`, `stage0IsoCheck`, and `stage0MaxLen`,
  returning `[ok, cnt, L_dem]` in `pOut` and the new heap pointer `h + n + 2 * m`, in
  `O(n + m * (narrowMaxCapLimbs I + 1) + 1)` steps.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling

namespace MinCostFlow.NarrowProg

/-! ### `stage0IsoCheck` -/

/-- Scan all `n` vertices and check that every isolated vertex (`label[v] = 0`) has demand limb
length `0` (`I.d v = 0`). Returns `1` iff `isolatedCheck I hv = true`, `0` otherwise. -/
wram_def stage0IsoCheck (pLabel, pDems, n) {
  off := 0
  for v in 0 .. n {
    if mem[pLabel + v] == 0 {
      if 0 < mem[pDems + off + 1] {
        return 0
      }
    }
    off := off + 3
  }
  return 1
}

/-- Specification of `stage0IsoCheck`. -/
def stage0IsoCheckSpec (w : ℕ) : Spec { I : Instance // I.IsValid } where
  pre := fun ⟨I, hv⟩ args => ⨆ (pLabel : ℕ) (pDems : ℕ),
    ⌜args = [pLabel, pDems, I.n] ∧
      pDems + 3 * I.n ≤ 2 ^ w ∧ 3 * I.n < 2 ^ w ∧ 3 < 2 ^ w⌝ *
    Assn.list pLabel (List.ofFn (FlowReduction.shiftedGraph I hv).endpointLabels.table) *
    (∏ v ∈ Finset.range I.n,
      Assn.list (pDems + v * 3) (if h : v < I.n then demRec I ⟨v, h⟩ else []))
  post := fun ⟨I, hv⟩ args r => ⨆ (pLabel : ℕ) (pDems : ℕ),
    ⌜args = [pLabel, pDems, I.n] ∧
      (r = 1 ∧ FlowReduction.isolatedCheck I hv = true ∨
       r = 0 ∧ (∀ f, ¬ I.IsFeasible f))⌝ *
    Assn.list pLabel (List.ofFn (FlowReduction.shiftedGraph I hv).endpointLabels.table) *
    (∏ v ∈ Finset.range I.n,
      Assn.list (pDems + v * 3) (if h : v < I.n then demRec I ⟨v, h⟩ else []))

theorem stage0IsoCheck_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage0IsoCheck) :
    Meets w p f ((stage0IsoCheckSpec w).withCost fun d _ => 60 * d.1.n + 30) := by
  sep_enter ⟨I, hv⟩ with hpD_fit h3n hw3
  set k := narrowLimbWidth I
  have hk : 1 ≤ k := one_le_narrowLimbWidth I
  have hb : 1 < 2 ^ k := by have := two_le_pow hk; omega
  sep_step
  sep_for fun v =>
    ⟨[pLabel, pDems, I.n, v * 3, v],
      v ≤ I.n ∧ ∀ (j : ℕ) (hj : j < I.n), j < v →
        0 < (FlowReduction.shiftedGraph I hv).endpointLabels.table ⟨j, hj⟩ ∨ I.d j = 0,
      50 * (I.n - v) + 10,
      [Assn.list pLabel (List.ofFn (FlowReduction.shiftedGraph I hv).endpointLabels.table),
       ∏ j ∈ Finset.range I.n,
         Assn.list (pDems + j * 3) (if h : j < I.n then demRec I ⟨j, h⟩ else [])]⟩
  · have hmem : v ∈ Finset.range I.n := Finset.mem_range.mpr hhi
    let vf : Fin I.n := ⟨v, hhi⟩
    have hpDv_fit : pDems + v * 3 + 3 ≤ 2 ^ w := by
      have : (v + 1) * 3 ≤ I.n * 3 := Nat.mul_le_mul_right 3 (by omega)
      omega
    have htab_len : v < (List.ofFn (FlowReduction.shiftedGraph I hv).endpointLabels.table).length := by
      simp [hhi]
    have htab_get : (List.ofFn (FlowReduction.shiftedGraph I hv).endpointLabels.table)[v]'htab_len =
        (FlowReduction.shiftedGraph I hv).endpointLabels.table vf := by simp [vf]
    have hoff_eq : v * 3 + 3 = (v + 1) * 3 := by ring
    have hoff_lt : v * 3 + 3 < 2 ^ w := by omega
    sep_step
    · rw [htab_get] at hcond
      sep_apply Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (pDems + j * 3) (if h : j < I.n then demRec I ⟨j, h⟩ else []))
      have hcur : Assn.list (pDems + v * 3) (if h : v < I.n then demRec I ⟨v, h⟩ else []) =
          Assn.list (pDems + v * 3) (demRec I vf) := by simp [vf, hhi]
      have hdem_len : (demRec I vf).length = 3 := rfl
      sep_apply hcur
      sep_step
      · simp only [demRec, List.getElem_cons_zero, List.getElem_cons_succ] at hcond_1
        have hdv_ne : I.d v ≠ 0 := by
          intro h0; simp [vf, h0] at hcond_1
        have hfalse : FlowReduction.isolatedCheck I hv = false := by
          by_contra hne
          have htrue : FlowReduction.isolatedCheck I hv = true := by
            cases hc : FlowReduction.isolatedCheck I hv <;> simp_all
          rcases (FlowReduction.isolatedCheck_iff I hv).mp htrue vf with hpos | hz
          · omega
          · exact hdv_ne hz
        have hinf : ∀ f, ¬ I.IsFeasible f :=
          FlowReduction.infeasible_of_isolatedCheck I hv hfalse
        sep_apply hcur.symm
        sep_apply (Assn.prod_eq_mul_erase hmem
          (fun j => Assn.list (pDems + j * 3) (if h : j < I.n then demRec I ⟨j, h⟩ else []))).symm
        sep_step
        exact Or.inr ⟨rfl, hinf⟩
      · simp only [demRec, List.getElem_cons_zero, List.getElem_cons_succ] at hcond_1
        have hdv_zero : I.d v = 0 := by
          have hdig : Nat.digits (2 ^ narrowLimbWidth I) (I.d vf).natAbs = [] :=
            List.eq_nil_of_length_eq_zero (by omega)
          have hnat : (I.d vf).natAbs = 0 := by
            have := Nat.ofDigits_digits (2 ^ narrowLimbWidth I) (I.d vf).natAbs
            rw [hdig] at this; simpa using this.symm
          exact Int.natAbs_eq_zero.mp hnat
        sep_apply hcur.symm
        sep_apply (Assn.prod_eq_mul_erase hmem
          (fun j => Assn.list (pDems + j * 3) (if h : j < I.n then demRec I ⟨j, h⟩ else []))).symm
        have hall_next : ∀ (j : ℕ) (hj : j < I.n), j < v + 1 →
            0 < (FlowReduction.shiftedGraph I hv).endpointLabels.table ⟨j, hj⟩ ∨ I.d j = 0 := by
          intro j hj hjv
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hjv) with hlt | rfl
          · exact hinv_1 j hj hlt
          · exact Or.inr hdv_zero
        sep_step; sep_step
    · rw [htab_get] at hcond
      have hpos : 0 < (FlowReduction.shiftedGraph I hv).endpointLabels.table vf := by omega
      have hall_next : ∀ (j : ℕ) (hj : j < I.n), j < v + 1 →
          0 < (FlowReduction.shiftedGraph I hv).endpointLabels.table ⟨j, hj⟩ ∨ I.d j = 0 := by
        intro j hj hjv
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hjv) with hlt | rfl
        · exact hinv_1 j hj hlt
        · exact Or.inl hpos
      sep_step; sep_step
  · have htrue : FlowReduction.isolatedCheck I hv = true :=
      (FlowReduction.isolatedCheck_iff I hv).mpr fun v => hinv_1 v.val v.isLt v.isLt
    sep_step
    exact Or.inl ⟨rfl, htrue⟩

/-! ### `stage0MaxLen` -/

/-- Compute `L_dem = 1 + max` over all edge `lower`/`upper` limb lengths and all active vertex
demand limb lengths. Runs in `O(m + cnt + 1)` steps (touching no isolated vertex). -/
wram_def stage0MaxLen (pEdges, pDems, pActive, m, cnt) {
  mx := 0
  off := 0
  for i in 0 .. m {
    a := mem[pEdges + off + 3]
    if mx < a { mx := a }
    b := mem[pEdges + off + 6]
    if mx < b { mx := b }
    off := off + 11
  }
  for c in 0 .. cnt {
    v := mem[pActive + c]
    a := mem[pDems + 3 * v + 1]
    if mx < a { mx := a }
  }
  return mx + 1
}

/-- Named value for `stage0MaxLenSpec`. -/
structure Stage0MaxLenData where
  I : Instance
  hv : I.IsValid
  act : List ℕ
  actTail : List ℕ

/-- Specification of `stage0MaxLen`. -/
def stage0MaxLenSpec (w : ℕ) : Spec Stage0MaxLenData where
  pre d args := ⨆ (pEdges : ℕ) (pDems : ℕ) (pActive : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    ⌜args = [pEdges, pDems, pActive, d.I.m, el.count] ∧
      ActiveInv el d.act ∧ el.count ≤ 2 * d.I.m ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pDems + 3 * d.I.n ≤ 2 ^ w ∧ 3 * d.I.n < 2 ^ w ∧
      narrowMaxCapLimbs d.I + 1 < 2 ^ w ∧ 10 < 2 ^ w⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else [])) *
    (∏ v ∈ Finset.range d.I.n,
      Assn.list (pDems + v * 3) (if h : v < d.I.n then demRec d.I ⟨v, h⟩ else [])) *
    Assn.list pActive (d.act ++ d.actTail)
  post d args L_dem := ⨆ (pEdges : ℕ) (pDems : ℕ) (pActive : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, pDems, pActive, d.I.m, el.count] ∧
      1 ≤ L_dem ∧ L_dem ≤ narrowMaxCapLimbs d.I + 1 ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) (d.I.edge e).lower.natAbs).length < L_dem ∧
        (Nat.digits (2 ^ k) (d.I.edge e).upper.natAbs).length < L_dem) ∧
      (∀ (c : ℕ) (hc : c < d.act.length),
        (Nat.digits (2 ^ k) (d.I.d (d.act[c]'hc)).natAbs).length < L_dem)⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else [])) *
    (∏ v ∈ Finset.range d.I.n,
      Assn.list (pDems + v * 3) (if h : v < d.I.n then demRec d.I ⟨v, h⟩ else [])) *
    Assn.list pActive (d.act ++ d.actTail)

theorem stage0MaxLen_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage0MaxLen) :
    Meets w p f ((stage0MaxLenSpec w).withCost fun d _ => 220 * d.I.m + 50) := by
  sep_enter ⟨I, hv, act, actTail⟩ with hact hcnt_le hpE_fit h11m hpD_fit h3n hL_lt hw10
  set el := (FlowReduction.shiftedGraph I hv).endpointLabels
  have hk : 1 ≤ narrowLimbWidth I := one_le_narrowLimbWidth I
  sep_step; sep_step
  sep_for (fun i (t : ℕ × ℕ × ℕ) =>
    ⟨[pEdges, pDems, pActive, I.m, el.count, t.1, i * 11, i, t.2.1, t.2.2, 0, 0],
      i ≤ I.m ∧ t.1 ≤ narrowMaxCapLimbs I ∧
        ∀ (j : ℕ) (hj : j < I.m), j < i →
          (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨j, hj⟩).lower.natAbs).length ≤ t.1 ∧
          (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨j, hj⟩).upper.natAbs).length ≤ t.1,
      70 * (I.m - i) + 130 * I.m + 25,
      [∏ j ∈ Finset.range I.m,
         Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else []),
       ∏ v ∈ Finset.range I.n,
         Assn.list (pDems + v * 3) (if h : v < I.n then demRec I ⟨v, h⟩ else []),
       Assn.list pActive (act ++ actTail)]⟩) with ⟨mx, a, b⟩
  · have hmem : i ∈ Finset.range I.m := Finset.mem_range.mpr hhi
    let e : Fin I.m := ⟨i, hhi⟩
    have hrec_len : (edgeRec I e).length = 11 := rfl
    have hlo_le : (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length ≤
        narrowMaxCapLimbs I :=
      digits_length_mono (by have := two_le_pow hk; omega) (lower_natAbs_le_maxCapacity' I e)
    have hhi_le : (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length ≤
        narrowMaxCapLimbs I :=
      digits_length_mono (by have := two_le_pow hk; omega) (upper_natAbs_le_maxCapacity' I e)
    have hpEi_fit : pEdges + i * 11 + 11 ≤ 2 ^ w := by
      have : (i + 1) * 11 ≤ I.m * 11 := Nat.mul_le_mul_right 11 (by omega)
      omega
    have hoff_eq : i * 11 + 11 = (i + 1) * 11 := by ring
    have hoff_lt : i * 11 + 11 < 2 ^ w := by omega
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else []))
    have hcur : Assn.list (pEdges + i * 11) (if h : i < I.m then edgeRec I ⟨i, h⟩ else []) =
        Assn.list (pEdges + i * 11) (edgeRec I e) := by simp [e, hhi]
    sep_apply hcur
    sep_step
    simp only [edgeRec, List.getElem_cons_zero, List.getElem_cons_succ] at ha_1
    subst a_1
    sep_step
    · sep_step; sep_step
      simp only [edgeRec, List.getElem_cons_zero, List.getElem_cons_succ] at hb_1
      subst b_1
      sep_apply hcur.symm
      sep_apply (Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else []))).symm
      sep_step
      · have hall1 : ∀ (j : ℕ) (hj : j < I.m), j < i + 1 →
            (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨j, hj⟩).lower.natAbs).length ≤
              (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length ∧
            (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨j, hj⟩).upper.natAbs).length ≤
              (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length := by
          intro j hj hji
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hji) with hlt | rfl
          · have := hinv_2 j hj hlt; omega
          · have he : (⟨j, hj⟩ : Fin I.m) = e := rfl
            rw [he]; exact ⟨by omega, le_rfl⟩
        sep_step; sep_step
      · have hall2 : ∀ (j : ℕ) (hj : j < I.m), j < i + 1 →
            (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨j, hj⟩).lower.natAbs).length ≤
              (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length ∧
            (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨j, hj⟩).upper.natAbs).length ≤
              (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length := by
          intro j hj hji
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hji) with hlt | rfl
          · have := hinv_2 j hj hlt; omega
          · have he : (⟨j, hj⟩ : Fin I.m) = e := rfl
            rw [he]; exact ⟨le_rfl, by omega⟩
        sep_step; sep_step
    · sep_step; sep_step
      simp only [edgeRec, List.getElem_cons_zero, List.getElem_cons_succ] at hb_1
      subst b_1
      sep_apply hcur.symm
      sep_apply (Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else []))).symm
      sep_step
      · have hall3 : ∀ (j : ℕ) (hj : j < I.m), j < i + 1 →
            (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨j, hj⟩).lower.natAbs).length ≤
              (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length ∧
            (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨j, hj⟩).upper.natAbs).length ≤
              (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length := by
          intro j hj hji
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hji) with hlt | rfl
          · have := hinv_2 j hj hlt; omega
          · have he : (⟨j, hj⟩ : Fin I.m) = e := rfl
            rw [he]; exact ⟨by omega, le_rfl⟩
        sep_step; sep_step
      · have hall4 : ∀ (j : ℕ) (hj : j < I.m), j < i + 1 →
            (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨j, hj⟩).lower.natAbs).length ≤ mx ∧
            (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨j, hj⟩).upper.natAbs).length ≤ mx := by
          intro j hj hji
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hji) with hlt | rfl
          · exact hinv_2 j hj hlt
          · have he : (⟨j, hj⟩ : Fin I.m) = e := rfl
            rw [he]; exact ⟨by omega, by omega⟩
        sep_step; sep_step
  · have hedge_all : ∀ e : Fin I.m,
        (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length ≤ mx ∧
        (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length ≤ mx :=
      fun e => hinv_2 e.val e.isLt e.isLt
    sep_for (fun c (t : ℕ × ℕ × ℕ) =>
      ⟨[pEdges, pDems, pActive, I.m, el.count, t.1, I.m * 11, I.m, t.2.2, b, c, t.2.1],
        c ≤ el.count ∧ mx ≤ t.1 ∧ t.1 ≤ narrowMaxCapLimbs I ∧
          ∀ (j : ℕ) (hj : j < act.length), j < c →
            (Nat.digits (2 ^ narrowLimbWidth I) (I.d (act[j]'hj)).natAbs).length ≤ t.1,
        55 * (el.count - c) + 10,
        [∏ j ∈ Finset.range I.m,
           Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else []),
         ∏ u ∈ Finset.range I.n,
           Assn.list (pDems + u * 3) (if h : u < I.n then demRec I ⟨u, h⟩ else []),
         Assn.list pActive (act ++ actTail)]⟩) with ⟨mx2, v, a2⟩
    · have hc_act : c < act.length := by rw [hact.1]; exact hhi
      obtain ⟨hvlt, _⟩ := hact.2 c hc_act
      set vv := act[c]'hc_act
      have hact_len : c < (act ++ actTail).length := by simp; omega
      have hact_get : (act ++ actTail)[c]'hact_len = vv := by
        rw [List.getElem_append_left hc_act]
      have hmem : vv ∈ Finset.range I.n := Finset.mem_range.mpr hvlt
      have hdem_len : (demRec I ⟨vv, hvlt⟩).length = 3 := rfl
      have hd_le : (Nat.digits (2 ^ narrowLimbWidth I) (I.d vv).natAbs).length ≤
          narrowMaxCapLimbs I :=
        digits_length_mono (by have := two_le_pow hk; omega)
          (demand_natAbs_le_maxCapacity' I hv ⟨vv, hvlt⟩)
      have h3v_lt : 3 * vv < 2 ^ w := by omega
      have h3v_eq : 3 * vv = vv * 3 := by ring
      have hpDv_fit : pDems + vv * 3 + 3 ≤ 2 ^ w := by
        have : (vv + 1) * 3 ≤ I.n * 3 := Nat.mul_le_mul_right 3 (by omega)
        omega
      sep_step
      rw [hact_get] at hv_1; subst v_1
      sep_apply Assn.prod_eq_mul_erase hmem
        (fun u => Assn.list (pDems + u * 3) (if h : u < I.n then demRec I ⟨u, h⟩ else []))
      have hcur : Assn.list (pDems + vv * 3) (if h : vv < I.n then demRec I ⟨vv, h⟩ else []) =
          Assn.list (pDems + vv * 3) (demRec I ⟨vv, hvlt⟩) := by simp [hvlt]
      sep_apply hcur
      rw [← h3v_eq]
      sep_step
      rw [h3v_eq]
      simp only [demRec, List.getElem_cons_zero, List.getElem_cons_succ] at ha_1
      subst a_1
      sep_apply hcur.symm
      sep_apply (Assn.prod_eq_mul_erase hmem
        (fun u => Assn.list (pDems + u * 3) (if h : u < I.n then demRec I ⟨u, h⟩ else []))).symm
      sep_step
      · have hdem1 : ∀ (j : ℕ) (hj : j < act.length), j < c + 1 →
            (Nat.digits (2 ^ narrowLimbWidth I) (I.d (act[j]'hj)).natAbs).length ≤
              (Nat.digits (2 ^ narrowLimbWidth I) (I.d vv).natAbs).length := by
          intro j hj hjc
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hjc) with hlt | rfl
          · have := hinv_3_3 j hj hlt; omega
          · exact le_rfl
        sep_step
      · have hdem2 : ∀ (j : ℕ) (hj : j < act.length), j < c + 1 →
            (Nat.digits (2 ^ narrowLimbWidth I) (I.d (act[j]'hj)).natAbs).length ≤ mx2 := by
          intro j hj hjc
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hjc) with hlt | rfl
          · exact hinv_3_3 j hj hlt
          · omega
        sep_step
    · have hret_lt : mx2 + 1 < 2 ^ w := by omega
      have hedge_lt : ∀ e : Fin I.m,
          (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length < mx2 + 1 ∧
          (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length < mx2 + 1 := fun e => by
        have := hedge_all e; omega
      have hdem_lt : ∀ (c : ℕ) (hc : c < act.length),
          (Nat.digits (2 ^ narrowLimbWidth I) (I.d (act[c]'hc)).natAbs).length < mx2 + 1 := fun c hc => by
        have hc' : c < el.count := by rw [← hact.1]; exact hc
        have := hinv_3_3 c hc hc'; omega
      sep_step

/-! ### Top-level `stage0Check` -/

/-- Heap space consumed by `stage0Check`: `pLabel` (`n` words) + `pActive` (`2 * m` words). -/
def stage0CheckSpace (I : Instance) : ℕ :=
  I.n + 2 * I.m

private theorem split_free_check {h n m w : ℕ} (hfit : h + (n + 2 * m) ≤ 2 ^ w) :
    Assn.free h (2 ^ w - h) =
      Assn.list h (List.replicate n 0) *
      Assn.list (h + n) (List.replicate (2 * m) 0) *
      Assn.free (h + n + 2 * m) (2 ^ w - (h + n + 2 * m)) := by
  have hsplit : 2 ^ w - h = n + (2 * m + (2 ^ w - (h + n + 2 * m))) := by omega
  rw [hsplit, Assn.free_add', Assn.free_add']
  simp only [Assn.free, mul_assoc]

private theorem list_split_three {p : ℕ} {buf : List ℕ} (hlen : buf.length = 3) :
    Assn.list p buf =
      (p ↦ buf[0]'(by omega)) * (p + 1 ↦ buf[1]'(by omega)) * (p + 2 ↦ buf[2]'(by omega)) := by
  rcases buf with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | xs⟩⟩⟩ <;> simp at hlen ⊢
  simp only [mul_assoc, show p + 1 + 1 = p + 2 by omega]

private theorem list_join_three' (p a0 a1 a2 : ℕ) :
    (p ↦ a0) * (p + 1 ↦ a1) * (p + 2 ↦ a2) = Assn.list p [a0, a1, a2] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one, mul_assoc, show p + 1 + 1 = p + 2 by omega]

/-- Run all Stage 0 feasibility checks (`lower ≤ upper`, endpoint labels, `isolatedCheck`) and
compute `L_dem`. Writes `[ok, cnt, L_dem]` into `pOut` (`ok = 0` certifies infeasibility) and
returns `h + n + 2 * m`. -/
wram_def stage0Check (chkCaps labels isoCheck maxLen : ℕ) (pEdges, pDems, m, n, pOut, h) {
  pLabel := h
  pActive := h + n
  hNext := pActive + 2 * m
  ok := chkCaps(pEdges, m)
  if ok == 0 {
    mem[pOut] := 0
    return hNext
  }
  cnt := labels(pEdges, pLabel, pActive, m)
  ok := isoCheck(pLabel, pDems, n)
  if ok == 0 {
    mem[pOut] := 0
    return hNext
  }
  Ldem := maxLen(pEdges, pDems, pActive, m, cnt)
  mem[pOut] := 1
  mem[pOut + 1] := cnt
  mem[pOut + 2] := Ldem
  return hNext
}

/-- Specification of `stage0Check`. -/
def stage0CheckSpec (w : ℕ) : Spec ({ I : Instance // I.IsValid } × List ℕ) where
  pre := fun (⟨I, _⟩, outBuf) args => ⨆ (pEdges : ℕ) (pDems : ℕ) (pOut : ℕ) (h : ℕ),
    ⌜args = [pEdges, pDems, I.m, I.n, pOut, h] ∧ outBuf.length = 3 ∧
      pEdges + 11 * I.m ≤ 2 ^ w ∧ 11 * I.m < 2 ^ w ∧
      pDems + 3 * I.n ≤ 2 ^ w ∧ 3 * I.n < 2 ^ w ∧
      narrowMaxCapLimbs I + 1 < 2 ^ w ∧
      h + stage0CheckSpace I < 2 ^ w ∧ 10 < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode I) *
    (∏ i ∈ Finset.range I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < I.m then edgeRec I ⟨i, hlt⟩ else [])) *
    (∏ v ∈ Finset.range I.n,
      Assn.list (pDems + v * 3) (if hlt : v < I.n then demRec I ⟨v, hlt⟩ else [])) *
    Assn.list pOut outBuf * Assn.free h (2 ^ w - h)
  post := fun (⟨I, hv⟩, _) args h' => ⨆ (pEdges : ℕ) (pDems : ℕ) (pOut : ℕ) (h : ℕ)
      (ok : ℕ) (cnt : ℕ) (L_dem : ℕ) (act : List ℕ) (actTail : List ℕ),
    let el := (FlowReduction.shiftedGraph I hv).endpointLabels
    let k := narrowLimbWidth I
    ⌜args = [pEdges, pDems, I.m, I.n, pOut, h] ∧ h' = h + stage0CheckSpace I ∧
      ((ok = 0 ∧ ∀ f, ¬ I.IsFeasible f) ∨
       (ok = 1 ∧ (∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper) ∧
         FlowReduction.isolatedCheck I hv = true ∧
         cnt = el.count ∧ cnt ≤ 2 * I.m ∧ ActiveInv el act ∧
         act.length + actTail.length = 2 * I.m ∧
         1 ≤ L_dem ∧ L_dem ≤ narrowMaxCapLimbs I + 1 ∧
         (∀ e : Fin I.m,
           (Nat.digits (2 ^ k) (I.edge e).lower.natAbs).length < L_dem ∧
           (Nat.digits (2 ^ k) (I.edge e).upper.natAbs).length < L_dem) ∧
         (∀ (c : ℕ) (hc : c < act.length),
           (Nat.digits (2 ^ k) (I.d (act[c]'hc)).natAbs).length < L_dem)))⌝ *
    Assn.list 0 (narrowEncode I) *
    (∏ i ∈ Finset.range I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < I.m then edgeRec I ⟨i, hlt⟩ else [])) *
    (∏ v ∈ Finset.range I.n,
      Assn.list (pDems + v * 3) (if hlt : v < I.n then demRec I ⟨v, hlt⟩ else [])) *
    Assn.list pOut [ok, cnt, L_dem] *
    (if ok = 1 then
      Assn.list h (List.ofFn el.table) * Assn.list (h + I.n) (act ++ actTail)
    else Assn.gc) *
    Assn.free h' (2 ^ w - h')

theorem stage0Check_meets {w : ℕ} {p : Program} {f chkCaps labels isoCheck maxLen : ℕ}
    {Tc : Instance → ℕ} {Tl Ti Tm : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0Check chkCaps labels isoCheck maxLen))
    (hc : Meets w p chkCaps ((stage0CheckCapsSpec w).withCost fun d _ => Tc d.1))
    (hl : Meets w p labels ((stage0LabelsSpec w).withCost fun d _ => Tl d.1.m))
    (hi : Meets w p isoCheck ((stage0IsoCheckSpec w).withCost fun d _ => Ti d.1.n))
    (hm : Meets w p maxLen ((stage0MaxLenSpec w).withCost fun d _ => Tm d.I.m)) :
    Meets w p f ((stage0CheckSpec w).withCost fun x _ =>
      Tc x.1.1 + Tl x.1.1.m + Ti x.1.1.n + Tm x.1.1.m + 100) := by
  sep_enter ⟨⟨I, hv⟩, outBuf⟩ with hout hpE_fit h11m hpD_fit h3n hL_lt hfit hw10
  have hfit' : h + (I.n + 2 * I.m) < 2 ^ w := hfit
  have hret_eq : h + I.n + 2 * I.m = h + stage0CheckSpace I := by
    dsimp only [stage0CheckSpace]; omega
  sep_apply split_free_check (h := h) (n := I.n) (m := I.m) (w := w) (by omega)
  sep_apply list_split_three (p := pOut) hout
  sep_step; sep_step; sep_step
  subst pActive hNext
  generalize hF1 :
    ((∏ v ∈ Finset.range I.n,
        Assn.list (pDems + v * 3) (if hlt : v < I.n then demRec I ⟨v, hlt⟩ else [])) *
     (pOut ↦ outBuf[0]'(by omega)) * (pOut + 1 ↦ outBuf[1]'(by omega)) *
     (pOut + 2 ↦ outBuf[2]'(by omega)) *
     Assn.list h (List.replicate I.n 0) * Assn.list (h + I.n) (List.replicate (2 * I.m) 0) *
     Assn.free (h + I.n + 2 * I.m) (2 ^ w - (h + I.n + 2 * I.m))) = F1
  sep_apply hF1
  sep_step from (⟨I, hv⟩ : { J : Instance // J.IsValid }) with hcap_res
  subst F1
  sep_norm
  sep_step
  · rcases hcap_res with ⟨h1, _⟩ | ⟨_, hinf⟩
    · omega
    · sep_step; sep_step
      sep_apply list_join_three' pOut 0 (outBuf[1]'(by omega)) (outBuf[2]'(by omega))
      sep_step
      sep_exists pEdges, pDems, pOut, h, 0, (outBuf[1]'(by omega)), (outBuf[2]'(by omega)),
        ([] : List ℕ), ([] : List ℕ)
      simp only [Nat.zero_ne_one, ↓reduceIte]
      sep_entail
      · exact Or.inl ⟨rfl, hinf⟩
  · rcases hcap_res with ⟨_, hcaps⟩ | ⟨h0, _⟩
    · sep_step
      generalize hF2 :
        (Assn.list 0 (narrowEncode I) *
         (∏ v ∈ Finset.range I.n,
            Assn.list (pDems + v * 3) (if hlt : v < I.n then demRec I ⟨v, hlt⟩ else [])) *
         (pOut ↦ outBuf[0]'(by omega)) * (pOut + 1 ↦ outBuf[1]'(by omega)) *
         (pOut + 2 ↦ outBuf[2]'(by omega)) *
         Assn.free (h + I.n + 2 * I.m) (2 ^ w - (h + I.n + 2 * I.m))) = F2
      sep_apply hF2
      sep_step from (⟨I, hv⟩ : { J : Instance // J.IsValid }) with hact_inv hact_len hcnt_le
      subst F2
      sep_norm
      generalize hF3 :
        (Assn.list 0 (narrowEncode I) *
         (∏ i ∈ Finset.range I.m,
            Assn.list (pEdges + i * 11) (if hlt : i < I.m then edgeRec I ⟨i, hlt⟩ else [])) *
         Assn.list (h + I.n) (act ++ actTail) *
         (pOut ↦ outBuf[0]'(by omega)) * (pOut + 1 ↦ outBuf[1]'(by omega)) *
         (pOut + 2 ↦ outBuf[2]'(by omega)) *
         Assn.free (h + I.n + 2 * I.m) (2 ^ w - (h + I.n + 2 * I.m))) = F3
      sep_apply hF3
      sep_step from (⟨I, hv⟩ : { J : Instance // J.IsValid }) with hiso_res
      subst F3
      sep_norm
      sep_step
      · rcases hiso_res with ⟨h1, _⟩ | ⟨_, hinf⟩
        · omega
        · sep_step; sep_step
          sep_apply list_join_three' pOut 0 (outBuf[1]'(by omega)) (outBuf[2]'(by omega))
          sep_step
          sep_exists pEdges, pDems, pOut, h, 0, (outBuf[1]'(by omega)), (outBuf[2]'(by omega)),
            ([] : List ℕ), ([] : List ℕ)
          simp only [Nat.zero_ne_one, ↓reduceIte]
          sep_entail
          · exact Or.inl ⟨rfl, hinf⟩
      · rcases hiso_res with ⟨_, hiso⟩ | ⟨h0, _⟩
        · sep_step
          generalize hF4 :
            (Assn.list 0 (narrowEncode I) *
             Assn.list h (List.ofFn (FlowReduction.shiftedGraph I hv).endpointLabels.table) *
             (pOut ↦ outBuf[0]'(by omega)) * (pOut + 1 ↦ outBuf[1]'(by omega)) *
             (pOut + 2 ↦ outBuf[2]'(by omega)) *
             Assn.free (h + I.n + 2 * I.m) (2 ^ w - (h + I.n + 2 * I.m))) = F4
          sep_apply hF4
          sep_step from (⟨I, hv, act, actTail⟩ : Stage0MaxLenData) with
            _hcnt_eq hL1 hLle hedge_lt hdem_lt
          subst F4
          sep_norm
          sep_step; sep_step; sep_step
          sep_apply list_join_three' pOut 1 (FlowReduction.shiftedGraph I hv).endpointLabels.count Ldem
          sep_step
          sep_exists pEdges, pDems, pOut, h, 1,
            (FlowReduction.shiftedGraph I hv).endpointLabels.count, Ldem, act, actTail
          simp only [↓reduceIte]
          sep_entail
          · exact Or.inr ⟨rfl, hcaps, hiso, rfl, hcnt_le, hact_inv, hact_len,
              hL1, hLle, hedge_lt, hdem_lt⟩
        · omega
    · omega

theorem stage0Check_meets_direct {w : ℕ} {p : Program}
    {f cmp sle oneCap chkCaps scanEnd labels isoCheck maxLen : ℕ}
    (hw : 2 < 2 ^ w)
    (hp : p.procs[f]? = some (stage0Check chkCaps labels isoCheck maxLen))
    (hcmp : p.procs[cmp]? = some limbsCmp)
    (hsle : p.procs[sle]? = some (signedLimbsLe cmp))
    (h1 : p.procs[oneCap]? = some (stage0CheckOneCap sle))
    (hcc : p.procs[chkCaps]? = some (stage0CheckCaps oneCap))
    (hse : p.procs[scanEnd]? = some stage0ScanEnd)
    (hl : p.procs[labels]? = some (stage0Labels scanEnd))
    (hi : p.procs[isoCheck]? = some stage0IsoCheck)
    (hm : p.procs[maxLen]? = some stage0MaxLen) :
    Meets w p f ((stage0CheckSpec w).withCost fun x _ =>
      (40 * narrowMaxCapLimbs x.1.1 + 570) * x.1.1.m + 60 * x.1.1.n + 340) := by
  have hcmpM := limbsCmp_meets (w := w) hw hcmp
  have hsleM := signedLimbsLe_meets (w := w) (Tcmp := fun L => 40 * L + 20) hw hsle hcmpM
  have h1M := stage0CheckOneCap_meets (w := w) (Tsle := fun L => 40 * L + 20 + 50) h1 hsleM
  have hccM := stage0CheckCaps_meets (w := w) (T1 := fun L => 40 * L + 20 + 50 + 60)
    (fun a b h => by omega) hcc h1M
  have hseM := stage0ScanEnd_meets (w := w) hse
  have hlM := stage0Labels_meets (w := w) (Tse := fun m => 80 * m + 40) hl hseM
  have hiM := stage0IsoCheck_meets (w := w) hi
  have hmM := stage0MaxLen_meets (w := w) hm
  exact (stage0Check_meets
    (Tc := fun I => (40 * narrowMaxCapLimbs I + 20 + 50 + 60 + 55) * I.m + 40)
    (Tl := fun m => 2 * (80 * m + 40) + 40)
    (Ti := fun n => 60 * n + 30)
    (Tm := fun m => 220 * m + 50)
    hp hccM hlM hiM hmM).withCost_mono fun x _ => by nlinarith

theorem stage0Check_meetsO {w : ℕ} {p : Program}
    {f cmp sle oneCap chkCaps scanEnd labels isoCheck maxLen : ℕ}
    (hw : 2 < 2 ^ w)
    (hp : p.procs[f]? = some (stage0Check chkCaps labels isoCheck maxLen))
    (hcmp : p.procs[cmp]? = some limbsCmp)
    (hsle : p.procs[sle]? = some (signedLimbsLe cmp))
    (h1 : p.procs[oneCap]? = some (stage0CheckOneCap sle))
    (hcc : p.procs[chkCaps]? = some (stage0CheckCaps oneCap))
    (hse : p.procs[scanEnd]? = some stage0ScanEnd)
    (hl : p.procs[labels]? = some (stage0Labels scanEnd))
    (hi : p.procs[isoCheck]? = some stage0IsoCheck)
    (hm : p.procs[maxLen]? = some stage0MaxLen) :
    MeetsO w p f (stage0CheckSpec w) fun x _ =>
      x.1.1.n + x.1.1.m * (narrowMaxCapLimbs x.1.1 + 1) + 1 :=
  MeetsO.of_meets (stage0Check_meets_direct hw hp hcmp hsle h1 hcc hse hl hi hm)
    ⟨570, fun ⟨x, _⟩ => by dsimp only; nlinarith⟩

/-! ### Polymorphic module -/

/-- Procedure names for `stage0CheckMod`, polymorphic over any name type `ι`. -/
structure Stage0CheckNames (ι : Type) where
  limbsCmp : ι
  signedLimbsLe : ι
  checkOneCap : ι
  checkCaps : ι
  scanEnd : ι
  labels : ι
  isoCheck : ι
  maxLen : ι
  stage0Check : ι

/-- Self-contained polymorphic module for Stage 0 item 2 (`stage0Check`). -/
def stage0CheckMod {ι : Type} (names : Stage0CheckNames ι) : Module ι :=
  ⟨[(names.limbsCmp, fun _ => limbsCmp),
    (names.signedLimbsLe, fun idx => signedLimbsLe (idx names.limbsCmp)),
    (names.checkOneCap, fun idx => stage0CheckOneCap (idx names.signedLimbsLe)),
    (names.checkCaps, fun idx => stage0CheckCaps (idx names.checkOneCap)),
    (names.scanEnd, fun _ => stage0ScanEnd),
    (names.labels, fun idx => stage0Labels (idx names.scanEnd)),
    (names.isoCheck, fun _ => stage0IsoCheck),
    (names.maxLen, fun _ => stage0MaxLen),
    (names.stage0Check, fun idx =>
      stage0Check (idx names.checkCaps) (idx names.labels)
        (idx names.isoCheck) (idx names.maxLen))]⟩

theorem stage0CheckMod_noRand {ι : Type} (names : Stage0CheckNames ι) :
    (stage0CheckMod names).NoRand := by
  wram_no_rand

theorem stage0CheckMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {names : Stage0CheckNames ι} (hw : 2 < 2 ^ w)
    (hp : (stage0CheckMod names).Placed p idx) :
    MeetsO w p (idx names.stage0Check) (stage0CheckSpec w) fun x _ =>
      x.1.1.n + x.1.1.m * (narrowMaxCapLimbs x.1.1 + 1) + 1 :=
  stage0Check_meetsO hw
    (hp.get (n := names.stage0Check) (b := fun idx =>
      stage0Check (idx names.checkCaps) (idx names.labels)
        (idx names.isoCheck) (idx names.maxLen)) (by simp [stage0CheckMod]))
    (hp.get (n := names.limbsCmp) (b := fun _ => limbsCmp) (by simp [stage0CheckMod]))
    (hp.get (n := names.signedLimbsLe) (b := fun idx =>
      signedLimbsLe (idx names.limbsCmp)) (by simp [stage0CheckMod]))
    (hp.get (n := names.checkOneCap) (b := fun idx =>
      stage0CheckOneCap (idx names.signedLimbsLe)) (by simp [stage0CheckMod]))
    (hp.get (n := names.checkCaps) (b := fun idx =>
      stage0CheckCaps (idx names.checkOneCap)) (by simp [stage0CheckMod]))
    (hp.get (n := names.scanEnd) (b := fun _ => stage0ScanEnd) (by simp [stage0CheckMod]))
    (hp.get (n := names.labels) (b := fun idx =>
      stage0Labels (idx names.scanEnd)) (by simp [stage0CheckMod]))
    (hp.get (n := names.isoCheck) (b := fun _ => stage0IsoCheck) (by simp [stage0CheckMod]))
    (hp.get (n := names.maxLen) (b := fun _ => stage0MaxLen) (by simp [stage0CheckMod]))

end MinCostFlow.NarrowProg
